import Hedgehog

/-!
A counter tested with commands as types (`Hedgehog.Command`), in both
modes.  `Increment` asserts that the counter stays at or below 100; no
single command breaks that, and the given order does not either.
-/

namespace HedgehogTest.Madhouse

open Hedgehog

structure State where
  value : Nat := 0
  deriving Repr, Inhabited

/-- What commands are built from. -/
structure Context where
  maxIncrement : Nat

structure Increment where
  amount : Nat

instance : Command Increment State Context Id where
  check _ _ _ := true
  apply _ c s := do
    let s := { s with value := s.value + c.amount }
    ensure (s.value ≤ 100) s!"counter exceeded 100: {s.value}"
    pure s
  label c := s!"INCREMENT({c.amount})"
  build ctx := Increment.mk <$> Gen.nat (.constant 1 ctx.maxIncrement)

structure Reset where

instance : Command Reset State Context Id where
  check _ _ s := s.value > 0
  apply _ _ s := pure { s with value := 0 }
  label _ := "RESET"
  build _ := pure {}

/-- Adding `Reset` did not touch `Increment`, and adding a third command
would touch neither. -/
def counter (mode : Mode) : Property Id :=
  scenario mode (Context.mk 50) [
    Command.gen Increment,
    Command.gen Reset,
    Command.fixed (Increment.mk 42)]

/-- The amounts of the increments a counterexample executed, if it
executed nothing else. -/
def amounts (c : Counterexample) : Option (List Nat) :=
  (c.journal.toList.filterMap fun
    | .note text => some text
    | _ => none).mapM fun text =>
      ((text.dropPrefix? "executed INCREMENT(").bind
        (·.dropSuffix? ")")).bind (·.toNat?)

/-- Whether madhouse mode finds the overflow on each of twenty seeds,
shrunk to increments that pass 100 by exactly one. -/
def shrinks : Bool :=
  (List.range 20).all fun i =>
    match ((counter .madhouse).report (Seed.ofNat i)).status with
    | .failed c => (amounts c).map List.sum == some 101
    | _ => false

/-- The state and journal after the commands, run from the default
state. -/
def execute (commands : List (CommandWrapper State Id)) :
    Option (Nat × List String) :=
  match Id.run ((executeCommands commands default).run.run #[]) with
  | (.ok s, journal) => some (s.value, journal.toList.map fun
    | .note text => text
    | .input value => value
    | .label name .. => name)
  | (.error _, _) => none

/-- The labels the scenario draws on two hundred seeds. -/
def selections (mode : Mode) : List (Option (List String)) :=
  (List.range 200).map fun i =>
    match ((counter mode).withTests 1 |>.withShrinks 0
      |>.test.run.run #[]).run 99 (Seed.ofNat i) |>.value with
    | some (_, journal) => journal.toList.head?.map fun
      | .input value => value.splitOn ", "
      | .note text => [text]
      | .label name .. => [name]
    | none => none

/-- The numbers of resets a scenario draws on two hundred seeds, at the
largest size. -/
def lengths (p : Property Id) : List (Option Nat) :=
  (List.range 200).map fun i =>
    match (p.withShrinks 0 |>.test.run.run #[]).run 99 (Seed.ofNat i)
      |>.value with
    | some (_, journal) => journal.toList.head?.map fun
      | .input value => (value.splitOn "RESET").length - 1
      | _ => 0
    | none => none

/-- The counter from a start between 0 and `top`, with a setup that
adds `extra`. -/
def startsAt (top extra : Nat) (mode : Mode) : Property Id :=
  scenarioFrom (State.mk <$> Gen.nat (.constant 0 top)) mode
    (Context.mk 1) [Command.fixed (Increment.mk 1)] (.constant 1 1)
    fun s => do
      annotate s!"started at {s.value}"
      pure { s with value := s.value + extra }

/-- The start a failing scenario reports. -/
def start (r : Report) : Option String :=
  match r.status with
  | .failed c => c.journal.toList.findSome? fun
    | .note text => text.dropPrefix? "started at " |>.map (·.toString)
    | _ => none
  | _ => none

/-- What is left to spend. -/
structure Budget where
  left : Nat := 100
  deriving Repr, Inhabited

/-- Spend no more than is left: generated for the state, and `next`
says what it leaves. -/
structure Spend where
  amount : Nat

instance : Command Spend Budget Unit Id where
  apply _ c s := do
    ensure (c.amount ≤ s.left) s!"overspent by {c.amount - s.left}"
    pure { left := s.left - c.amount }
  label c := s!"SPEND({c.amount})"
  build _ := pure ⟨0⟩
  next _ c s := { left := s.left - c.amount }
  buildIn _ s := Spend.mk <$> Gen.nat (.constant 0 s.left)

/-- The same without `next`: every command is generated for the start
state. -/
structure SpendBlind where
  amount : Nat

instance : Command SpendBlind Budget Unit Id where
  apply _ c s := do
    ensure (c.amount ≤ s.left) s!"overspent by {c.amount - s.left}"
    pure { left := s.left - c.amount }
  label c := s!"SPEND({c.amount})"
  build _ := pure ⟨0⟩
  buildIn _ s := SpendBlind.mk <$> Gen.nat (.constant 0 s.left)

/-- The message a scenario fails with on a seed. -/
def failsWith (p : Property Id) (i : Nat) : Option String :=
  match (p.report (Seed.ofNat i)).status with
  | .failed c => some c.failure.message
  | _ => none

/-- A command that reads its limit from the context when it runs. -/
structure Bounded where
  amount : Nat

instance : Command Bounded State Context Id where
  apply ctx c s := do
    ensure (c.amount ≤ ctx.maxIncrement) "more than the context allows"
    pure { s with value := s.value + c.amount }
  label c := s!"BOUNDED({c.amount})"
  build _ := pure ⟨7⟩

/-- A command that may run, and tells its next state, by the context. -/
structure Gated where
  amount : Nat

instance : Command Gated State Context Id where
  check ctx c _ := c.amount ≤ ctx.maxIncrement
  apply _ c s := pure { s with value := s.value + c.amount }
  label c := s!"GATED({c.amount})"
  build _ := pure ⟨7⟩
  next ctx _ s := { s with value := s.value + ctx.maxIncrement }

/-- The context of the facts below. -/
def ctx : Context := ⟨50⟩

def facts : List (String × Bool) := [
  ("a command whose check fails is skipped",
    execute [Command.wrap ctx ({} : Reset), Command.wrap ctx (Increment.mk 5),
      Command.wrap ctx ({} : Reset), Command.wrap ctx ({} : Reset)]
      == some (0, ["executed INCREMENT(5)", "executed RESET"])),
  ("commands run in order", execute [Command.wrap ctx (Increment.mk 5),
    Command.wrap ctx (Increment.mk 6)]
      == some (11, ["executed INCREMENT(5)", "executed INCREMENT(6)"])),
  ("a failed assertion stops the scenario",
    execute [Command.wrap ctx (Increment.mk 101),
      Command.wrap ctx (Increment.mk 1)] == none),
  ("no commands", execute [] == some (0, [])),
  ("check is given the context",
    execute [Command.wrap ⟨7⟩ (Gated.mk 7)]
        == some (7, ["executed GATED(7)"])
      && execute [Command.wrap ⟨6⟩ (Gated.mk 7)] == some (0, [])),
  ("next is given the context",
    ((Command.wrap ⟨5⟩ (Gated.mk 1) : CommandWrapper State Id).next
      ⟨3⟩).value == 8),
  ("apply is given the context of the scenario",
    execute [Command.wrap ⟨7⟩ (Bounded.mk 7)]
        == some (7, ["executed BOUNDED(7)"])
      && execute [Command.wrap ⟨6⟩ (Bounded.mk 7)] == none
      && (scenario .deterministic (Context.mk 7) [Command.gen Bounded]
        |>.report (Seed.ofNat 0)).ok
      && !(scenario .deterministic (Context.mk 6) [Command.gen Bounded]
        |>.report (Seed.ofNat 0)).ok),
  ("a wrapper shows its label",
    reprStr (Command.wrap ctx (Increment.mk 5) : CommandWrapper State Id)
      == "INCREMENT(5)"),
  ("fixed keeps the command", (List.range 20).all fun i =>
    ((Command.fixed (Increment.mk 42) (Context.mk 50) default).run 50
      (Seed.ofNat i)).value.map (·.label) == some "INCREMENT(42)"),
  ("gen builds from the context", (List.range 200).all fun i =>
    ((Command.gen Increment (Context.mk 3) default).run 50
      (Seed.ofNat i)).value.any fun c =>
        ["INCREMENT(1)", "INCREMENT(2)", "INCREMENT(3)"].contains c.label),
  ("deterministic mode runs one test",
    ((counter .deterministic).report (Seed.ofNat 0)).run
      == ⟨1, 0, .ok, #[]⟩),
  ("deterministic mode keeps the order", (selections .deterministic).all
    fun x => x.any fun labels => labels.length == 3
      && (labels[0]?.any (·.startsWith "[INCREMENT("))
      && labels[1]? == some "RESET"
      && labels[2]? == some "INCREMENT(42)]"),
  ("madhouse mode draws 1 to 15 commands", (selections .madhouse).all
    fun x => x.any fun labels => 1 ≤ labels.length && labels.length ≤ 15),
  ("madhouse mode reorders", (selections .madhouse).any
    fun x => x.any fun labels => labels[0]?.any (·.startsWith "[RESET")),
  ("madhouse mode runs a hundred tests",
    (counter .madhouse).config.tests == 100),
  ("madhouse mode takes a range of lengths",
    (lengths (scenario .madhouse (Context.mk 1) [Command.gen Reset]
      (.constant 20 30))).all
        fun n => n.any fun n => 20 ≤ n && n ≤ 30),
  ("deterministic mode ignores the range",
    (lengths (scenario .deterministic (Context.mk 1) [Command.gen Reset]
      (.constant 20 30))).all (· == some 1)),
  ("a scenario passes from a start that leaves room",
    (List.range 20).all fun i =>
      ((startsAt 99 0 .madhouse).report (Seed.ofNat i)).ok),
  ("a scenario starts from the generated state, shrunk",
    (List.range 20).all fun i =>
      start ((startsAt 200 0 .madhouse).report (Seed.ofNat i))
        == some "100"),
  ("the setup runs before the first command",
    (List.range 20).all fun i =>
      start ((startsAt 200 40 .madhouse).report (Seed.ofNat i))
        == some "60"),
  ("a command is generated for the state the ones before lead to",
    (List.range 20).all fun i =>
      ((scenario .madhouse () [Command.gen Spend] (.constant 20 30)).report
        (Seed.ofNat i)).ok),
  ("deterministic mode generates for that state too",
    (List.range 20).all fun i =>
      ((scenario .deterministic () (List.replicate 20
        (Command.gen Spend))).report (Seed.ofNat i)).ok),
  ("without next a command is generated for the start state, and a \
    failure shrinks to the least",
    (List.range 20).all fun i =>
      failsWith (scenario .madhouse () [Command.gen SpendBlind]
        (.constant 20 30)) i == some "overspent by 1"),
  ("next is the same state unless given",
    ((Command.wrap ctx (Increment.mk 5) : CommandWrapper State Id).next
      ⟨3⟩).value == 3),
  ("a wrapper has the command's next",
    ((Command.wrap () (Spend.mk 5) : CommandWrapper Budget Id).next
      ⟨8⟩).left == 3),
  ("gen builds for the state", (List.range 200).all fun i =>
    ((Command.gen Spend () ⟨2⟩).run 50 (Seed.ofNat i)).value.any fun c =>
      ["SPEND(0)", "SPEND(1)", "SPEND(2)"].contains c.label),
  ("deterministic mode starts from the generated state too",
    (List.range 20).any fun i =>
      !((startsAt 200 0 .deterministic).report (Seed.ofNat i)).ok)]

end HedgehogTest.Madhouse
