module

public import Hedgehog.Property

/-!
# Running properties

The runner draws test cases at growing sizes.  When one fails it walks
the shrink tree, each time into the first shrink that still fails, and
reports the smallest failure with the size and seed that reproduce it.

`Property.report` is a function of the property and a seed, in the
property's own monad; for a pure property it is a pure function.  `check`
runs it in `IO`, prints the report, and throws on failure, so `#eval
check p` fails the build and a `main` that calls it fails `lake test`.
-/

@[expose] public section

namespace Hedgehog

/-- A failing test case, shrunk. -/
structure Counterexample where
  size : Size
  seed : Seed
  shrinks : Nat
  journal : Journal
  failure : Failure
  deriving Repr, BEq, Inhabited

inductive Status where
  | ok
  | gaveUp
  | failed (counterexample : Counterexample)
  deriving Repr, BEq, Inhabited

/-- The outcome of checking a property. -/
structure Report where
  /-- Test cases that passed. -/
  tests : Nat
  /-- Test cases that were discarded. -/
  discards : Nat
  status : Status
  deriving Repr, BEq, Inhabited

def Report.ok (r : Report) : Bool :=
  r.status == .ok

namespace Property

variable {m : Type → Type} [Monad m]

/-- A node of a property's shrink tree: discarded, failed while
generating, or ready to run. -/
abbrev Case (m : Type → Type) :=
  Option (Except Failure (TestT m Unit) × Journal)

inductive Outcome where
  | discard
  | pass
  | fail (journal : Journal) (failure : Failure)

def runCase : Case m → m Outcome
  | none => pure .discard
  | some (.error e, journal) => pure (.fail journal e)
  | some (.ok test, journal) => do
    match ← test.run.run journal with
    | (.ok (), _) => pure .pass
    | (.error e, journal) => pure (.fail journal e)

/-- The first shrink that fails. -/
def firstFailure :
    List (Unit → Tree (Case m)) →
      m (Option (Tree (Case m) × Journal × Failure))
  | [] => pure none
  | c :: cs => do
    let t := c ()
    match ← runCase t.value with
    | .fail journal e => pure (some (t, journal, e))
    | _ => firstFailure cs

/-- Walk down failing shrinks until none fails or `fuel` runs out. -/
def shrink :
    (fuel shrinks : Nat) → Tree (Case m) → Journal → Failure →
      m (Nat × Journal × Failure)
  | 0, shrinks, _, journal, e => pure (shrinks, journal, e)
  | fuel + 1, shrinks, t, journal, e => do
    match ← firstFailure t.children with
    | none => pure (shrinks, journal, e)
    | some (t, journal, e) => shrink fuel (shrinks + 1) t journal e

def tree (p : Property m) (size : Size) (seed : Seed) : Tree (Case m) :=
  (p.test.run.run #[]).run size seed

/-- Run the test case of a size and seed, and shrink it if it fails. -/
def runTest (p : Property m) (size : Size) (seed : Seed) :
    m (Option Status) := do
  let t := p.tree size seed
  match ← runCase t.value with
  | .pass => pure (some .ok)
  | .discard => pure none
  | .fail journal e =>
    let (shrinks, journal, e) ← shrink p.config.shrinks 0 t journal e
    pure (some (.failed ⟨size, seed, shrinks, journal, e⟩))

def loop (p : Property m) :
    (fuel tests discards : Nat) → Size → Seed → m Report
  | 0, tests, discards, _, _ => pure ⟨tests, discards, .gaveUp⟩
  | fuel + 1, tests, discards, size, seed =>
    if tests ≥ p.config.tests then pure ⟨tests, discards, .ok⟩
    else if discards ≥ p.config.discards then
      pure ⟨tests, discards, .gaveUp⟩
    else do
      let (s1, s2) := seed.split
      let size' := if size ≥ 99 then 0 else size + 1
      match ← p.runTest size s1 with
      | some .ok => loop p fuel (tests + 1) discards size' s2
      | some status => pure ⟨tests, discards, status⟩
      | none => loop p fuel tests (discards + 1) size' s2

/-- Check the property on test cases drawn from `seed`. -/
def report (p : Property m) (seed : Seed) : m Report :=
  loop p (p.config.tests + p.config.discards + 1) 0 0 0 seed

/-- Check the one test case of a size and seed, as a failure report
names them. -/
def recheck (p : Property m) (size : Size) (seed : Seed) : m Report := do
  match ← p.runTest size seed with
  | some .ok => pure ⟨1, 0, .ok⟩
  | some status => pure ⟨0, 0, status⟩
  | none => pure ⟨0, 1, .gaveUp⟩

end Property

namespace Report

def count (n : Nat) (noun : String) : String :=
  if n = 1 then s!"1 {noun}" else s!"{n} {noun}s"

/-- The report as `check` prints it. -/
def render (name : String) (r : Report) : String :=
  match r.status with
  | .ok => s!"  ✓ {name} passed {count r.tests "test"}."
  | .gaveUp =>
    s!"  ⚐ {name} gave up after {count r.discards "discard"}, \
      passed {count r.tests "test"}."
  | .failed c =>
    let logs := c.journal.toList.map fun
      | .input value => s!"forAll {hang 11 value}"
      | .note text => hang 4 text
    let body := logs ++ [hang 4 c.failure.message]
    let seed := s!"⟨{c.seed.value}, {c.seed.gamma}⟩"
    s!"  ✗ {name} failed after {count (r.tests + 1) "test"} and \
      {count c.shrinks "shrink"}.\n\n    \
      {"\n    ".intercalate body}\n\n    \
      This failure can be reproduced by running:\n    \
      > recheck {c.size} {seed} <property>"

end Report

/-- Pure properties run in `IO`. -/
instance : MonadLift Id IO where
  monadLift x := pure x.run

section Check

variable {m : Type → Type} [Monad m] [MonadLiftT m IO]

def finish (name : String) (r : Report) : IO Unit :=
  if r.ok then IO.println (r.render name)
  else throw (IO.userError ("\n" ++ r.render name))

/-- Check a property, print the report, and throw if it did not pass.
The seed is random unless given. -/
def check (p : Property m) (name : String := "property")
    (seed : Option Seed := none) : IO Unit := do
  let seed ← match seed with
    | some seed => pure seed
    | none => Seed.random
  finish name (← liftM (p.report seed))

/-- Run again the test case a failure report names. -/
def recheck (size : Size) (seed : Seed) (p : Property m)
    (name : String := "property") : IO Unit := do
  finish name (← liftM (p.recheck size seed))

/-- Check each property and print its report; `true` if all passed. -/
def checkGroup (name : String) (properties : List (String × Property m)) :
    IO Bool := do
  IO.println s!"━━━ {name} ━━━"
  let mut ok := true
  for (name, p) in properties do
    let r ← liftM (p.report (← Seed.random))
    IO.println (r.render name)
    ok := ok && r.ok
  pure ok

end Check
end Hedgehog
