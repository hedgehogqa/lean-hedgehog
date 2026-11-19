import Examples.LeanVM

/-!
What the examples of `Examples/LeanVM.lean` shrink to.
-/

namespace HedgehogTest.LeanVM

open Hedgehog

/-- The counterexample of a report: what `forAll` logged, then the
failure. -/
def counterexample (r : Report) : Option (List String × String) :=
  match r.status with
  | .failed c => some (c.journal.toList.filterMap (fun
    | .input value => some value
    | _ => none), c.failure.message)
  | _ => none

/-- Whether the property fails on each of twenty seeds with one of the
counterexamples. -/
def finds (p : Property Id) (expected : List (List String × String)) :
    Bool :=
  (List.range 20).all fun i =>
    (counterexample (p.report (Seed.ofNat i))).any expected.contains

/-- The scenarios that are as small as can be: a jump and the steps
that then leave the program, or eight steps. -/
def smallest : List (List String × String) :=
  let steps (n : Nat) := List.replicate n "NEXT"
  let shown (labels : List String) := "[" ++ ", ".intercalate labels ++ "]"
  let scenarios := shown (steps 8) :: (List.range 8).map fun target =>
    shown (s!"JUMP({target})" :: steps (8 - target))
  scenarios.map fun scenario => ([scenario], "pc left the program")

def facts : List (String × Bool) := [
  ("a size past two bytes shrinks to 65536", finds sizeRoundTrips
    [(["65536"], "=== failed\n  lhs: some 0\n  rhs: some 65536")]),
  ("an overwritten cell shrinks to two writes", finds memory.property
    [(["([], [Op.set 0 0, Op.set 0 1])"],
      "=== failed\n  lhs: 1\n  rhs: 0"),
     (["([], [Op.set 0 1, Op.set 0 0])"],
      "=== failed\n  lhs: 0\n  rhs: 1")]),
  ("the program passes in the order given", (List.range 200).all fun i =>
    ((program .deterministic).report (Seed.ofNat i)).ok),
  ("madhouse shrinks to a jump and the steps that leave",
    finds (program .madhouse) smallest),
  ("the report of a size past two bytes",
    ((sizeRoundTrips.report (Seed.ofNat 0)).render "size round trips")
      == "  ✗ size round trips failed after 2 tests and 16 shrinks.\n\n    \
          forAll 65536\n    === failed\n      lhs: some 0\n      \
          rhs: some 65536\n\n    \
          This failure can be reproduced by running:\n    \
          > recheck 1 ⟨4446439630527111738, 15321243935405834545⟩ \
          <property>")]

end HedgehogTest.LeanVM
