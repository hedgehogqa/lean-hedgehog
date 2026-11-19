import Hedgehog

/-!
A counter tested against a model, with transitions as one type
(`Hedgehog.StateMachine`).  The system under test is a mutable reference
in `IO`.
-/

namespace HedgehogTest.Counter

open Hedgehog

/-- The model: a counter that stops at `max`. -/
structure Counter where
  value : Int
  max : Int
  deriving Repr

/-- Every operation, in one type. -/
inductive Transition where
  | inc
  | dec
  | reset
  deriving Repr, BEq

def Transition.name : Transition → String
  | .inc => "inc"
  | .dec => "dec"
  | .reset => "reset"

def model : Model Counter Transition where
  initState := pure ⟨0, 3⟩
  transitions _ := Gen.element [.inc, .dec, .reset]
  apply s
    | .inc => if s.value < s.max then { s with value := s.value + 1 } else s
    | .dec => { s with value := s.value - 1 }
    | .reset => { s with value := 0 }

/-- The system under test.  With `saturate := false` it has a bug: it
counts past `max`. -/
def machine (saturate : Bool) :
    StateMachine Counter Transition (IO.Ref Int) IO where
  toModel := model
  initSut s := IO.mkRef s.value
  applySut sut s t := do
    match t with
    | .inc => sut.modify fun n => if saturate && n ≥ s.max then n else n + 1
    | .dec => sut.modify (· - 1)
    | .reset => sut.set 0
    pure sut
  invariants sut s := do
    (← sut.get) === s.value

def agrees : Property IO :=
  (machine true).property

/-- The buggy system, with the transitions logged by name. -/
def disagrees : Property IO := propertyM do
  let sm := machine false
  let (s, ts) ← forAllWith (fun x => toString (x.2.map Transition.name))
    (sm.toModel.sequence (.linear 1 50))
  pure (sm.run s ts)

/-- Whether the buggy system is caught on each of twenty seeds, with the
shortest sequence that shows the bug. -/
def shrinks : IO Bool :=
  (List.range 20).allM fun i => do
    match (← disagrees.report (Seed.ofNat i)).status with
    | .failed c => pure (c.journal[0]? == some (.input "[inc, inc, inc, inc]"))
    | _ => pure false

/-! A counter that may not go below zero: preconditions. -/

inductive Step where
  | inc
  | dec
  deriving Repr, BEq

def Step.name : Step → String
  | .inc => "inc"
  | .dec => "dec"

/-- The system is a count and whether it ever reached two.  It fails on
a `dec` below zero, which a valid sequence never asks for, and, when
`strict`, on a `dec` after two was reached. -/
def bounded (strict : Bool) : StateMachine Nat Step (Nat × Bool) Id where
  initState := pure 0
  transitions _ := Gen.element [.inc, .dec]
  preconditions s t := t == .inc || s > 0
  apply s
    | .inc => s + 1
    | .dec => s - 1
  initSut s := pure (s, false)
  applySut sut _ t := do
    match t with
    | .inc => pure (sut.1 + 1, sut.2 || sut.1 + 1 ≥ 2)
    | .dec =>
      ensure (sut.1 > 0) "below zero"
      ensure (!(strict && sut.2)) "dec after two"
      pure (sut.1 - 1, sut.2)
  invariants sut s := sut.1 === s

/-- Whether the strict system fails on each of twenty seeds with the
shortest valid sequence.  Were shrinks that break the precondition kept,
it would shrink to a lone `dec` and fail "below zero". -/
def shrinksWithinPreconditions : Bool :=
  (List.range 20).all fun i =>
    let sm := bounded true
    let p : Property Id := propertyM do
      let (s, ts) ← forAllWith (fun x => toString (x.2.map Step.name))
        (sm.toModel.sequence (.linear 1 50))
      pure (sm.run s ts)
    match (p.report (Seed.ofNat i)).status with
    | .failed c => c.journal == #[.input "[inc, inc, dec]"]
      && c.failure.message == "dec after two"
    | _ => false

/-- The sequences of a model on two hundred seeds, at size 99. -/
def sequences (range : Range Nat) : List (Option (Nat × List Step)) :=
  (List.range 200).map fun i =>
    (((bounded false).toModel.sequence range).run 99 (Seed.ofNat i)).value

/-- A model whose initial state is generated. -/
def startsAnywhere : Property Id :=
  let sm : StateMachine Nat Step Nat Id := {
    initState := Gen.nat (.linear 0 100)
    transitions := fun _ => pure .inc
    apply := fun s _ => s + 1
    initSut := pure
    applySut := fun sut _ _ => pure (sut + 1)
    invariants := fun sut s => do
      sut === s
      ensure (s < 50) }
  sm.property

def facts : IO (List (String × Bool)) := do
  let torn ← IO.mkRef 0
  let sm : StateMachine Counter Transition (IO.Ref Int) IO :=
    { machine true with teardown := fun _ => torn.modify (· + 1) }
  let report ← sm.property.report (Seed.ofNat 0)
  let buggy : StateMachine Counter Transition (IO.Ref Int) IO :=
    { machine false with teardown := fun _ => torn.modify (· + 1000) }
  let failing ← (buggy.property.withShrinks 0).report (Seed.ofNat 0)
  pure [
    ("teardown runs after each passing sequence",
      report.ok && (← torn.get) == 100 + 1000 * failing.tests),
    ("sequences respect the preconditions", (sequences (.linear 1 50)).all
      fun x => x.any fun (s, ts) => (bounded false).toModel.valid s ts),
    ("valid rejects a dec at zero",
      !(bounded false).toModel.valid 0 [.dec]
      && (bounded false).toModel.valid 0 [.inc, .dec]),
    ("sequences have a length in the range", (sequences (.constant 3 7)).all
      fun x => x.any fun (_, ts) => 3 ≤ ts.length && ts.length ≤ 7),
    ("sequences use the whole range", (sequences (.constant 3 7)).any
      fun x => x.any fun (_, ts) => ts.length == 7),
    ("the system agrees within the preconditions",
      ((bounded false).property.report (Seed.ofNat 0)).ok),
    ("shrinks stay within the preconditions", shrinksWithinPreconditions),
    ("the initial state shrinks", (List.range 20).all fun i =>
      match (startsAnywhere.report (Seed.ofNat i)).status with
      | .failed c => c.journal.toList.all fun
        | .input v =>
          let n := ((v.drop 1).takeWhile Char.isDigit).toString.toNat?
          n.any (· + (v.splitOn "Step.inc").length - 1 == 50)
        | _ => false
      | _ => false)]

end HedgehogTest.Counter
