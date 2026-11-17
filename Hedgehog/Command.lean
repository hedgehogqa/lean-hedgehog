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
`apply`, through a handle kept in the state or the context. -/
class Command (κ : Type) (σ χ : outParam Type)
    (m : outParam (Type → Type)) where
  /-- Whether the command may run in a state; always, unless given. -/
  check : κ → σ → Bool := fun _ _ => true
  /-- Run the command: the next state, or a failed assertion. -/
  apply : κ → σ → TestT m σ
  /-- The command as reports show it. -/
  label : κ → String
  /-- Generate the command. -/
  build : χ → Gen κ

/-- A command with its type forgotten, so commands of different types fit
in one list. -/
structure CommandWrapper (σ : Type) (m : Type → Type) where
  label : String
  check : σ → Bool
  apply : σ → TestT m σ

instance {σ : Type} {m : Type → Type} : Repr (CommandWrapper σ m) where
  reprPrec c _ := c.label

namespace Command

variable {κ σ χ : Type} {m : Type → Type}

def wrap [Command κ σ χ m] (c : κ) : CommandWrapper σ m :=
  ⟨label c, check c, apply c⟩

/-- A scenario entry: the command `κ`, generated. -/
def gen (κ : Type) [Command κ σ χ m] (ctx : χ) :
    Gen (CommandWrapper σ m) :=
  wrap <$> (build ctx : Gen κ)

/-- A scenario entry: this very command. -/
def fixed [Command κ σ χ m] (c : κ) (_ : χ) : Gen (CommandWrapper σ m) :=
  pure (wrap c)

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

/-- A scenario over the commands, from the default state.  A failing
scenario shrinks to fewer and smaller commands in both modes.  The
`deterministic` mode runs one test; `madhouse` runs sequences of 1 to 15
commands, a hundred times unless the configuration is changed. -/
def scenario [Inhabited σ] (mode : Mode) (ctx : χ)
    (commands : List (χ → Gen (CommandWrapper σ m))) : Property m :=
  let gens := commands.map (· ctx)
  let test (g : Gen (List (CommandWrapper σ m))) :
      PropertyM (TestT m Unit) := do
    let cs ← forAll g
    pure ((fun _ => ()) <$> executeCommands cs default)
  match mode with
  | .deterministic =>
    { config := { tests := 1 }, test := test (Gen.sequence gens) }
  | .madhouse =>
    { test := test (Gen.list (.linear 1 15) (Gen.choice gens)) }

end Scenario
end Hedgehog
