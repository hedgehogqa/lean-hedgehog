module

public import Hedgehog.Property

/-!
# Model-based testing: commands as types

The second way to test a stateful system, after Rust's madhouse-rs.
Each command is a type of its own with a `Command` instance: how to
generate it, when it may run, what it does and how it is shown, all in
one place.  A scenario is a list of commands, and nothing central lists
them all, so a new command edits no existing code.  This is the open side
of the expression problem, and what lets a suite grow to hundreds of
commands written by many people.

Commands are generated before any of them runs.  A command that must
fit the state gives `buildIn`, which takes it, and `next`, which says
what state the command leads to; the scenario moves the state by `next`
from one command to the one after.

A scenario runs in one of two modes.  `deterministic` runs the commands
once, in the order given, each skipped if its `check` fails.  `madhouse`
draws random sequences from the same commands: the chaos that finds what
a scripted order cannot.  `Mode.fromEnv` selects `madhouse` when the
environment has `MADHOUSE=1`, as madhouse-rs does.
-/

@[expose] public section

namespace Hedgehog

/-- A command `κ` on a state `σ`, built from a context `χ`, with effects
in `m`.  The state is the model; a system under test is driven from
`apply`, through a handle kept in the context or in the state.  Each
method that takes a command takes the context before it, but `label`,
so a command holds only what is its own. -/
class Command (κ : Type) (σ χ : outParam Type)
    (m : outParam (Type → Type)) where
  /-- Whether the command may run in a state; always, unless given. -/
  check : χ → κ → σ → Bool := fun _ _ _ => true
  /-- Run the command: the next state, or a failed assertion. -/
  apply : χ → κ → σ → TestT m σ
  /-- The command as reports show it. -/
  label : κ → String
  /-- Generate the command. -/
  build : χ → Gen κ
  /-- The state after the command, as far as can be told before it
  runs; the same state unless given.  A scenario generates the next
  command for this state, since `apply` has not run yet. -/
  next : χ → κ → σ → σ := fun _ _ s => s
  /-- Generate the command for a state: the start state, moved by the
  `next` of the commands before.  `build` unless given. -/
  buildIn : χ → σ → Gen κ := fun ctx _ => build ctx

/-- A command with its type forgotten, so commands of different types fit
in one list. -/
structure CommandWrapper (σ : Type) (m : Type → Type) where
  label : String
  check : σ → Bool
  apply : σ → TestT m σ
  next : σ → σ := id

instance {σ : Type} {m : Type → Type} : Repr (CommandWrapper σ m) where
  reprPrec c _ := c.label

namespace Command

variable {κ σ χ : Type} {m : Type → Type}

def wrap [Command κ σ χ m] (ctx : χ) (c : κ) : CommandWrapper σ m :=
  ⟨label c, check ctx c, apply ctx c, next ctx c⟩

/-- A scenario entry: the command `κ`, generated for a state. -/
def gen (κ : Type) [Command κ σ χ m] (ctx : χ) (s : σ) :
    Gen (CommandWrapper σ m) :=
  wrap ctx <$> (buildIn ctx s : Gen κ)

/-- A scenario entry: this very command. -/
def fixed [Command κ σ χ m] (c : κ) (ctx : χ) (_ : σ) :
    Gen (CommandWrapper σ m) :=
  pure (wrap ctx c)

end Command

/-- How a scenario orders its commands. -/
inductive Mode where
  /-- Each command once, in the order given. -/
  | deterministic
  /-- Random sequences of the commands. -/
  | madhouse
  deriving Repr, BEq, Inhabited

/-- `madhouse` if the environment has `MADHOUSE=1`. -/
def Mode.fromEnv : IO Mode := do
  pure (if (← IO.getEnv "MADHOUSE") == some "1" then .madhouse
    else .deterministic)

section Scenario

variable {σ χ : Type} {m : Type → Type} [Monad m]

/-- Run the commands in order from a state, skipping those whose `check`
fails.  The journal lists the ones that ran. -/
def executeCommands (commands : List (CommandWrapper σ m)) (s : σ) :
    TestT m σ :=
  commands.foldlM (init := s) fun s c =>
    if c.check s then do
      annotate s!"executed {c.label}"
      c.apply s
    else pure s

/-- The trees of the steps, each generated for the state the steps
before it lead to by `next`.  A step that discards ends the list, and
discards the whole. -/
def threaded (size : Size) :
    List (σ → Gen (CommandWrapper σ m)) → σ → Seed →
      List (Tree (Option (CommandWrapper σ m)))
  | [], _, _ => []
  | step :: steps, s, seed =>
    let (s1, s2) := seed.split
    let t := (step s).run size s1
    match t.value with
    | some c => t :: threaded size steps (c.next s) s2
    | none => [t]

/-- A command from each step, in order, from a state.  It shrinks by
removing commands while at least `atLeast` stay, and by shrinking one.
A command generated for a state that a removed command led to stays as
it was; its `check` skips it if it no longer may run. -/
def commandsFrom (steps : List (σ → Gen (CommandWrapper σ m)))
    (atLeast : Nat) (s : σ) : Gen (List (CommandWrapper σ m)) :=
  ⟨fun size seed =>
    (Tree.interleave (threaded size steps s seed)).map fun cs => do
      let cs ← cs.mapM id
      if atLeast ≤ cs.length then some cs else none⟩

/-- A scenario over the commands, from a generated state.  A failing
scenario shrinks to fewer and smaller commands in both modes, and to a
smaller state.  The `deterministic` mode runs one test; `madhouse` runs
sequences of a length in `range`, a hundred times unless the
configuration is changed.

Each command is generated for a state: the start state, moved by the
`next` of the commands before it, since no command has run yet.

`setup` runs in the test before the first command, on the generated
state: it is where a system under test is started and its handle put in
the state.  The state is not shown in a report, since it need not have
a `Repr`; `setup` may `annotate` it. -/
def scenarioFrom (init : Gen σ) (mode : Mode) (ctx : χ)
    (commands : List (χ → σ → Gen (CommandWrapper σ m)))
    (range : Range Nat := .linear 1 15)
    (setup : σ → TestT m σ := pure) : Property m :=
  let steps := commands.map (· ctx)
  let any (s : σ) := Gen.choice (steps.map (· s))
  let test (g : σ → Gen (List (CommandWrapper σ m))) :
      PropertyM (TestT m Unit) := do
    let s ← liftM init
    let cs ← forAll (g s)
    pure do
      let _ ← executeCommands cs (← setup s)
  match mode with
  | .deterministic =>
    { config := { tests := 1 }, test := test (commandsFrom steps 0) }
  | .madhouse =>
    { test := test fun s => Gen.sized fun size => do
        let n ← Gen.prune (Gen.nat range)
        commandsFrom (List.replicate n any) (range.lowerBound size) s }

/-- A scenario over the commands, from the default state. -/
def scenario [Inhabited σ] (mode : Mode) (ctx : χ)
    (commands : List (χ → σ → Gen (CommandWrapper σ m)))
    (range : Range Nat := .linear 1 15)
    (setup : σ → TestT m σ := pure) : Property m :=
  scenarioFrom (pure default) mode ctx commands range setup

end Scenario
end Hedgehog
