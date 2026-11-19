module

public import Hedgehog.Gen

/-!
# Properties

A property draws values with `forAll` and makes assertions about them.
`PropertyM` is the monad it is written in: assertions and a journal over
`Gen`, so the whole property has one shrink tree and a failing test case
shrinks with no help from the property's author.

A property that needs effects returns them: it generates in `PropertyM`,
then gives back a `TestT m Unit` for the runner to run in `m`, once for
the test case and once for each shrink it tries.
-/

@[expose] public section

namespace Hedgehog

/-- A line of a test's journal. -/
inductive JournalEntry where
  /-- A value drawn by `forAll`. -/
  | input (value : String)
  /-- Text added by `annotate`. -/
  | note (text : String)
  /-- A class of test cases named by `cover`, `classify`, `label` or
  `collect`: whether this case is in it, and the percentage of cases
  that must be. -/
  | label (name : String) (minimum : Nat) (covered : Bool)
  deriving Repr, BEq, Inhabited

/-- What a test logged, in order. -/
abbrev Journal := Array JournalEntry

/-- Why a test failed. -/
structure Failure where
  message : String
  deriving Repr, BEq, Inhabited

/-- A test over `m`: it may fail, and it keeps a journal that survives
the failure. -/
abbrev TestT (m : Type → Type) := ExceptT Failure (StateT Journal m)

/-- A test that generates: the monad of properties. -/
abbrev PropertyM := TestT Gen

section Test

variable {m : Type → Type} [Monad m] {α β : Type}

/-- Add a line to the journal, shown if the test fails. -/
def annotate (text : String) : TestT m Unit :=
  modify (·.push (.note text))

/-- Count the test case under `name` when `covered`, and require that
at least `minimum` percent of the test cases are.  The report lists
each name with its percentage, and a property whose tests all pass
still fails when a name stays below its minimum. -/
def cover (minimum : Nat) (name : String) (covered : Bool) :
    TestT m Unit :=
  modify (·.push (.label name minimum covered))

/-- Count the test case under `name` when `covered`.  The report shows
the percentage and requires none. -/
def classify (name : String) (covered : Bool) : TestT m Unit :=
  cover 0 name covered

/-- Count the test case under `name`. -/
def label (name : String) : TestT m Unit :=
  cover 0 name true

/-- Count the test case under the value, as `Repr` shows it. -/
def collect [Repr α] (x : α) : TestT m Unit :=
  label (reprStr x)

/-- Fail the test. -/
def failWith (message : String) : TestT m α :=
  throw ⟨message⟩

def failure : TestT m α :=
  failWith "failure"

def success : TestT m Unit :=
  pure ()

/-- Fail unless `b`.  (Haskell's `assert`; in Lean `assert` is a keyword
of `do` blocks.) -/
def ensure (b : Bool) (message : String := "ensure failed") :
    TestT m Unit :=
  if b then pure () else failWith message

/-- Indent the lines of `s` after the first by `n` spaces. -/
def hang (n : Nat) (s : String) : String :=
  ("\n" ++ "".pushn ' ' n).intercalate (s.splitOn "\n")

/-- Fail unless `x == y`, showing both. -/
def eq [BEq α] [Repr α] (x y : α) : TestT m Unit :=
  if x == y then pure ()
  else failWith
    s!"=== failed\n  lhs: {hang 7 (reprStr x)}\n  rhs: {hang 7 (reprStr y)}"

/-- Fail if `x == y`, showing both. -/
def ne [BEq α] [Repr α] (x y : α) : TestT m Unit :=
  if x != y then pure ()
  else failWith
    s!"/== failed\n  lhs: {hang 7 (reprStr x)}\n  rhs: {hang 7 (reprStr y)}"

/-- Bytes in hexadecimal, for `forAllWith`: a byte array has no `Repr`
in core, and as a list of numbers it fills a report. -/
def bytesHex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length = 1 then '0' :: digits else digits))

/-- Equality of the results of a decoder into `Except`, which core does
not give: `===` and `tripping` need it.  It is scoped, so only a file
that opens `Hedgehog` has it. -/
scoped instance {ε : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok x, .ok y => x == y
    | .error e, .error f => e == f
    | _, _ => false

@[inherit_doc] scoped infix:50 " === " => eq
@[inherit_doc] scoped infix:50 " /== " => ne

/-- Fail unless decoding what `encode` made of `x` gives `x` back. -/
def tripping {f : Type → Type} [Applicative f] [BEq (f α)] [Repr (f α)]
    (x : α) (encode : α → β) (decode : β → f α) : TestT m Unit :=
  decode (encode x) === pure x

end Test

/-- Run an action; an exception fails the test. -/
def evalIO {α : Type} (action : IO α) : TestT IO α := do
  match ← action.toBaseIO with
  | .ok x => pure x
  | .error e => failWith s!"exception: {e}"

/-- Discard the test case; the runner draws another. -/
def discard {α : Type} : PropertyM α :=
  liftM (Gen.discard : Gen α)

/-- Draw a value and log it as `render` shows it. -/
def forAllWith {α : Type} (render : α → String) (g : Gen α) :
    PropertyM α := do
  let x ← liftM g
  modify (·.push (.input (render x)))
  pure x

/-- Draw a value and log it. -/
def forAll {α : Type} [Repr α] (g : Gen α) : PropertyM α :=
  forAllWith reprStr g

/-- When a property is done. -/
structure PropertyConfig where
  /-- Test cases that must pass. -/
  tests : Nat := 100
  /-- Discarded test cases after which the runner gives up. -/
  discards : Nat := 100
  /-- Shrinks after which the runner reports what it has. -/
  shrinks : Nat := 1000
  deriving Repr, BEq, Inhabited

/-- A property: the generating part, which returns the part to run in
`m`. -/
structure Property (m : Type → Type) where
  config : PropertyConfig := {}
  test : PropertyM (TestT m Unit)

/-- A pure property. -/
def property (test : PropertyM Unit) : Property Id :=
  { test := (fun _ => pure ()) <$> test }

/-- A property whose assertions run in `m`. -/
def propertyM {m : Type → Type} (test : PropertyM (TestT m Unit)) :
    Property m :=
  { test }

namespace Property

variable {m : Type → Type}

def withTests (n : Nat) (p : Property m) : Property m :=
  { p with config.tests := n }

def withDiscards (n : Nat) (p : Property m) : Property m :=
  { p with config.discards := n }

def withShrinks (n : Nat) (p : Property m) : Property m :=
  { p with config.shrinks := n }

/-- The property in a monad that `m` lifts to, so that a pure property
and one with effects fit in one group. -/
def lift {n : Type → Type} [MonadLiftT m n] (p : Property m) :
    Property n :=
  { config := p.config
    test := (fun (test : TestT m Unit) =>
      (ExceptT.mk fun journal => liftM (test.run.run journal) :
        TestT n Unit)) <$> p.test }

end Property
end Hedgehog
