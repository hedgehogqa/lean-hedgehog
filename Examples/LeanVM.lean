import Hedgehog

/-!
# Three seeded bugs, in toys shaped after leanVM

A size on the wire, a memory whose cells are written once, and a
program counter: three toys shaped after parts of leanVM, each with a
bug put there on purpose.  None of these bugs was found in leanVM.
`lake exe examples` runs them, and `HedgehogTest/LeanVM.lean` checks
what they shrink to.

They are declared at the top level, with no namespace, so that a report
names `Op.set` and nothing longer.

## What stands in for what

leanVM itself is not here.  In the vocabulary of test doubles (Meszaros,
*xUnit Test Patterns*), each example replaces it with a *fake*: a small
working implementation, such as an array for the memory.  A fake has
real behavior, and that is what a property needs, since it calls the
system with inputs nobody chose in advance.

None of them is a stub or a mock.  A *stub* returns canned answers to
the calls a test expects; a *mock* is told beforehand which calls to
expect and fails the test on any other.  Both fix the conversation
ahead of time, which generated inputs do not allow.

Two more things are not doubles at all:

- The *model* of a state machine (`Model`, or the state of a `Command`)
  is the test's oracle: it says what the right answer is.  A fake
  replaces a dependency; a model judges the system.
- Each fake carries a *seeded fault*, a bug put there on purpose, so
  that there is something to find.  With the real system in the fake's
  place, the same properties would be tests of leanVM.
-/

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
  apply _ _ r := do
    ensure (r.pc + 1 < 8) "pc left the program"
    pure { pc := r.pc + 1 }
  label _ := "NEXT"
  build _ := pure {}

structure Jump where
  target : Nat

instance : Command Jump Registers Unit Id where
  apply _ c _ := pure { pc := c.target }
  label c := s!"JUMP({c.target})"
  build _ := Jump.mk <$> Gen.nat (.constant 0 7)

def program (mode : Mode) : Property Id :=
  scenario mode () [Command.gen Next, Command.gen Jump]
