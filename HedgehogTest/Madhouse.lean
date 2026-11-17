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
  check _ _ := true
  apply c s := do
    let s := { s with value := s.value + c.amount }
    ensure (s.value ≤ 100) s!"counter exceeded 100: {s.value}"
    pure s
  label c := s!"INCREMENT({c.amount})"
  build ctx := Increment.mk <$> Gen.nat (.constant 1 ctx.maxIncrement)

structure Reset where

instance : Command Reset State Context Id where
  check _ s := s.value > 0
  apply _ s := pure { s with value := 0 }
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
    | .input _ => none).mapM fun text =>
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
    | .input value => value)
  | (.error _, _) => none

/-- The labels the scenario draws on two hundred seeds. -/
def selections (mode : Mode) : List (Option (List String)) :=
  (List.range 200).map fun i =>
    match ((counter mode).withTests 1 |>.withShrinks 0
      |>.test.run.run #[]).run 99 (Seed.ofNat i) |>.value with
    | some (_, journal) => journal.toList.head?.map fun
      | .input value => value.splitOn ", "
      | .note text => [text]
    | none => none

def facts : List (String × Bool) := [
  ("a command whose check fails is skipped",
    execute [Command.wrap ({} : Reset), Command.wrap (Increment.mk 5),
      Command.wrap ({} : Reset), Command.wrap ({} : Reset)]
      == some (0, ["executed INCREMENT(5)", "executed RESET"])),
  ("commands run in order", execute [Command.wrap (Increment.mk 5),
    Command.wrap (Increment.mk 6)]
      == some (11, ["executed INCREMENT(5)", "executed INCREMENT(6)"])),
  ("a failed assertion stops the scenario",
    execute [Command.wrap (Increment.mk 101), Command.wrap (Increment.mk 1)]
      == none),
  ("no commands", execute [] == some (0, [])),
  ("a wrapper shows its label",
    reprStr (Command.wrap (Increment.mk 5) : CommandWrapper State Id)
      == "INCREMENT(5)"),
  ("fixed keeps the command", (List.range 20).all fun i =>
    ((Command.fixed (Increment.mk 42) (Context.mk 50)).run 50
      (Seed.ofNat i)).value.map (·.label) == some "INCREMENT(42)"),
  ("gen builds from the context", (List.range 200).all fun i =>
    ((Command.gen Increment (Context.mk 3)).run 50
      (Seed.ofNat i)).value.any fun c =>
        ["INCREMENT(1)", "INCREMENT(2)", "INCREMENT(3)"].contains c.label),
  ("deterministic mode runs one test",
    ((counter .deterministic).report (Seed.ofNat 0)).run == ⟨1, 0, .ok⟩),
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
    (counter .madhouse).config.tests == 100)]

end HedgehogTest.Madhouse
