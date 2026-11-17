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

end HedgehogTest.Madhouse
