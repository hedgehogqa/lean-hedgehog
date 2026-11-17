import HedgehogTest.Basic

/-!
The examples of `README.md`, word for word, and the counterexamples it
shows for them.  They are over-simplified from leanVM: a size on the
wire, a memory whose cells are written once, and a program counter.
Change them here and in `README.md` together.
-/

namespace HedgehogTest.Readme

open Hedgehog

/-- A size on the wire, in two bytes. -/
def encode (n : Nat) : List UInt8 :=
  [n.toUInt8, (n >>> 8).toUInt8]

def decode : List UInt8 → Option Nat
  | [a, b] => some (a.toNat + 256 * b.toNat)
  | _ => none

def sizeRoundTrips : Property Id := property do
  let n ← forAll (Gen.nat (.linear 0 (2 ^ 30)))
  tripping n encode decode

/-- SET: store a value in a cell. -/
inductive Op where
  | set (address value : Nat)
  deriving Repr

def memory : StateMachine (List (Nat × Nat)) Op (Array Nat) Id where
  initState := pure []
  transitions _ :=
    Op.set <$> Gen.nat (.linear 0 7) <*> Gen.nat (.linear 0 255)
  apply m
    | .set a v => if (m.lookup a).isSome then m else (a, v) :: m
  initSut _ := pure (Array.replicate 8 0)
  applySut cells _
    | .set a v => pure (cells.set! a v)
  invariants cells m :=
    for (a, v) in m do cells[a]! === v

structure Registers where
  pc : Nat := 0
  deriving Inhabited

structure Next where

instance : Command Next Registers Unit Id where
  apply _ r := do
    ensure (r.pc + 1 < 8) "pc left the program"
    pure { pc := r.pc + 1 }
  label _ := "NEXT"
  build _ := pure {}

structure Jump where
  target : Nat

instance : Command Jump Registers Unit Id where
  apply c _ := pure { pc := c.target }
  label c := s!"JUMP({c.target})"
  build _ := Jump.mk <$> Gen.nat (.constant 0 7)

def program (mode : Mode) : Property Id :=
  scenario mode () [Command.gen Next, Command.gen Jump]

/-- The counterexample of a report: what `forAll` logged, then the
failure. -/
def counterexample (r : Report) : Option (List String × String) :=
  match r.status with
  | .failed c => some (c.journal.toList.filterMap (fun
    | .input value => some value
    | .note _ => none), c.failure.message)
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
    [(["([], [HedgehogTest.Readme.Op.set 0 0, \
        HedgehogTest.Readme.Op.set 0 1])"],
      "=== failed\n  lhs: 1\n  rhs: 0"),
     (["([], [HedgehogTest.Readme.Op.set 0 1, \
        HedgehogTest.Readme.Op.set 0 0])"],
      "=== failed\n  lhs: 0\n  rhs: 1")]),
  ("the program passes in the order given", (List.range 200).all fun i =>
    ((program .deterministic).report (Seed.ofNat i)).ok),
  ("madhouse shrinks to a jump and the steps that leave",
    finds (program .madhouse) smallest),
  ("the report of the README",
    ((sizeRoundTrips.report (Seed.ofNat 0)).render "size round trips")
      == "  ✗ size round trips failed after 2 tests and 16 shrinks.\n\n    \
          forAll 65536\n    === failed\n      lhs: some 0\n      \
          rhs: some 65536\n\n    \
          This failure can be reproduced by running:\n    \
          > recheck 1 ⟨4446439630527111738, 15321243935405834545⟩ \
          <property>")]

end HedgehogTest.Readme
