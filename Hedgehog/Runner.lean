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

/-- A class of test cases, and how many of those that passed are in
it. -/
structure Label where
  name : String
  /-- The percentage of test cases that must be in the class. -/
  minimum : Nat
  count : Nat
  deriving Repr, BEq, Inhabited

/-- Whether a class has its minimum among `tests` test cases. -/
def Label.covered (l : Label) (tests : Nat) : Bool :=
  l.count * 100 ≥ l.minimum * tests

/-- The classes the test cases named, in the order they first did. -/
abbrev Coverage := Array Label

namespace Coverage

/-- The classes of one test case.  A class named twice is counted once,
and keeps the greater minimum. -/
def ofJournal (journal : Journal) : Coverage :=
  journal.foldl (init := #[]) fun coverage log =>
    match log with
    | .label name minimum covered =>
      let count := if covered then 1 else 0
      match coverage.findIdx? (·.name == name) with
      | some i => coverage.modify i fun l =>
        { l with minimum := max l.minimum minimum,
                 count := max l.count count }
      | none => coverage.push ⟨name, minimum, count⟩
    | _ => coverage

/-- Add the classes of one more test case. -/
def add (coverage one : Coverage) : Coverage :=
  one.foldl (init := coverage) fun coverage l =>
    match coverage.findIdx? (·.name == l.name) with
    | some i => coverage.modify i fun k =>
      { k with minimum := max k.minimum l.minimum,
               count := k.count + l.count }
    | none => coverage.push l

/-- Whether every class has its minimum. -/
def sufficient (coverage : Coverage) (tests : Nat) : Bool :=
  coverage.all (·.covered tests)

end Coverage

inductive Status where
  | ok
  | gaveUp
  /-- Every test case passed, and a class of `cover` has too few. -/
  | uncovered
  | failed (counterexample : Counterexample)
  deriving Repr, BEq, Inhabited

/-- The outcome of checking a property. -/
structure Report where
  /-- Test cases that passed. -/
  tests : Nat
  /-- Test cases that were discarded. -/
  discards : Nat
  status : Status
  /-- The classes of the test cases that passed. -/
  coverage : Coverage := #[]
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
  | pass (journal : Journal)
  | fail (journal : Journal) (failure : Failure)

def runCase : Case m → m Outcome
  | none => pure .discard
  | some (.error e, journal) => pure (.fail journal e)
  | some (.ok test, journal) => do
    match ← test.run.run journal with
    | (.ok (), journal) => pure (.pass journal)
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

/-- Run the test case of a size and seed, and shrink it if it fails.
A passing test case gives its classes, a discarded one nothing. -/
def runTest (p : Property m) (size : Size) (seed : Seed) :
    m (Option (Except Counterexample Coverage)) := do
  let t := p.tree size seed
  match ← runCase t.value with
  | .pass journal => pure (some (.ok (.ofJournal journal)))
  | .discard => pure none
  | .fail journal e =>
    let (shrinks, journal, e) ← shrink p.config.shrinks 0 t journal e
    pure (some (.error ⟨size, seed, shrinks, journal, e⟩))

def loop (p : Property m) :
    (fuel tests discards : Nat) → Coverage → Size → Seed → m Report
  | 0, tests, discards, coverage, _, _ =>
    pure ⟨tests, discards, .gaveUp, coverage⟩
  | fuel + 1, tests, discards, coverage, size, seed =>
    if tests ≥ p.config.tests then
      let status := if coverage.sufficient tests then .ok else .uncovered
      pure ⟨tests, discards, status, coverage⟩
    else if discards ≥ p.config.discards then
      pure ⟨tests, discards, .gaveUp, coverage⟩
    else do
      let (s1, s2) := seed.split
      let size' := if size ≥ 99 then 0 else size + 1
      match ← p.runTest size s1 with
      | some (.ok one) =>
        loop p fuel (tests + 1) discards (coverage.add one) size' s2
      | some (.error c) => pure ⟨tests, discards, .failed c, coverage⟩
      | none => loop p fuel tests (discards + 1) coverage size' s2

/-- Check the property on test cases drawn from `seed`. -/
def report (p : Property m) (seed : Seed) : m Report :=
  loop p (p.config.tests + p.config.discards + 1) 0 0 #[] 0 seed

/-- Check the one test case of a size and seed, as a failure report
names them.  One test case says nothing of coverage, so a minimum is
not required of it. -/
def recheck (p : Property m) (size : Size) (seed : Seed) : m Report := do
  match ← p.runTest size seed with
  | some (.ok one) => pure ⟨1, 0, .ok, one⟩
  | some (.error c) => pure ⟨0, 0, .failed c, #[]⟩
  | none => pure ⟨0, 1, .gaveUp, #[]⟩

end Property

namespace Report

def count (n : Nat) (noun : String) : String :=
  if n = 1 then s!"1 {noun}" else s!"{n} {noun}s"

/-- A count as a percentage of `tests`, to one decimal place. -/
def percent (n tests : Nat) : String :=
  let tenths := if tests = 0 then 0 else (n * 1000 + tests / 2) / tests
  s!"{tenths / 10}.{tenths % 10}%"

/-- One line for each class: its percentage and name, the minimum it
must have, and a mark when it has less. -/
def renderCoverage (r : Report) : String :=
  String.join (r.coverage.toList.map fun l =>
    let share := percent l.count r.tests
    let need := if l.minimum = 0 then ""
      else if l.covered r.tests then
        s!", at least {l.minimum}%"
      else s!", at least {l.minimum}% ✗"
    s!"\n    {"".pushn ' ' (6 - share.length)}{share} {l.name}{need}")

/-- The report as `check` prints it. -/
def render (name : String) (r : Report) : String :=
  match r.status with
  | .ok =>
    s!"  ✓ {name} passed {count r.tests "test"}.{renderCoverage r}"
  | .uncovered =>
    s!"  ✗ {name} passed {count r.tests "test"}, \
      with insufficient coverage.{renderCoverage r}"
  | .gaveUp =>
    s!"  ⚐ {name} gave up after {count r.discards "discard"}, \
      passed {count r.tests "test"}.{renderCoverage r}"
  | .failed c =>
    let logs := c.journal.toList.filterMap fun
      | .input value => some s!"forAll {hang 11 value}"
      | .note text => some (hang 4 text)
      | .label .. => none
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

/-- Print a line now: a run whose output goes to a file is watched as
it goes. -/
def say (text : String) : IO Unit := do
  IO.println text
  (← IO.getStdout).flush

def finish (name : String) (r : Report) : IO Unit :=
  if r.ok then say (r.render name)
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

/-- Which properties of a group to check, and how. -/
structure Selection where
  /-- Check only the properties whose name holds one of these; every
  property if there is none. -/
  only : List String := []
  /-- Check the one test case of this size and seed, as a failure
  report names them, in place of a whole run. -/
  recheck : Option (Size × Seed) := none
  deriving Repr, BEq, Inhabited

namespace Selection

/-- Whether a property of this name is checked. -/
def selects (s : Selection) (name : String) : Bool :=
  s.only.isEmpty || s.only.any fun part => (name.splitOn part).length > 1

/-- The size and seed of `"<size> <value> <gamma>"`, the three numbers
of the line `recheck <size> ⟨<value>, <gamma>⟩` of a report. -/
def parseRecheck (text : String) : Option (Size × Seed) :=
  match (text.splitOn " ").filter (· != "") |>.map String.toNat? with
  | [some size, some value, some gamma] =>
    some (size, ⟨UInt64.ofNat value, UInt64.ofNat gamma⟩)
  | _ => none

/-- The selection that the environment asks for: `HEDGEHOG_ONLY` holds
parts of names, separated by commas, and `HEDGEHOG_RECHECK` a size and
the two numbers of a seed.  With neither, every property is checked. -/
def fromEnv : IO Selection := do
  let only := match ← IO.getEnv "HEDGEHOG_ONLY" with
    | some text => (text.splitOn ",").filter (· != "")
    | none => []
  let recheck ← match ← IO.getEnv "HEDGEHOG_RECHECK" with
    | none => pure none
    | some text => match parseRecheck text with
      | some found => pure (some found)
      | none => throw (IO.userError
        s!"HEDGEHOG_RECHECK: expected a size and two numbers of a \
          seed, got {text.quote}")
  pure { only, recheck }

end Selection

/-- Check each selected property and print its report; `true` if all
passed.  With `mustFail`, `true` if each failed with a counterexample:
this is for a group of findings, whose properties state what the code
under test does not yet do. -/
def checkGroup (name : String) (properties : List (String × Property m))
    (select : Selection := {}) (mustFail : Bool := false) : IO Bool := do
  let selected := properties.filter fun (name, _) => select.selects name
  if selected.isEmpty then return true
  say s!"━━━ {name} ━━━"
  let mut ok := true
  for (name, p) in selected do
    let r ← match select.recheck with
      | some (size, seed) => liftM (p.recheck size seed)
      | none => liftM (p.report (← Seed.random))
    say (r.render name)
    let failed := match r.status with
      | .failed _ => true
      | _ => false
    ok := ok && (if mustFail then failed else r.ok)
  pure ok

end Check
end Hedgehog
