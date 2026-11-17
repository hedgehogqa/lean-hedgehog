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

end HedgehogTest.Counter
