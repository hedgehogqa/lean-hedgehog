# lean-hedgehog

<img src="img/hedgehog-logo.svg" width="128" alt="">

Property-based testing for Lean 4.

```lean
import Hedgehog
open Hedgehog

def reverseReverse : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 100) Gen.alpha)
  xs.reverse.reverse === xs

#eval check reverseReverse "reverse reverse"
```

In Lean a property can be proved, and a proof beats any number of
tests.  Hedgehog is for where there is no proof, or not yet: it checks
the property on generated inputs and shrinks a failure to a small
counterexample.

- Before proving: a counterexample found in a second saves the hours a
  false statement would take.
- For code that runs but is not proved: IO, FFI, a fast implementation
  next to its specification.
- For systems with state, tested against a model in two styles:
  - [transitions as one closed type][closed]
  - [commands as open types][open]
- With integrated shrinking, the idea from [Erlang QuickCheck][eqc]: a
  generator carries its own shrinks, so there is no shrinker to write
  and a shrunk value keeps the generator's invariants.

[eqc]: https://www.quviq.com/documentation/eqc/eqc_gen.html
[closed]: https://blog.nikosbaxevanis.com/2025/01/10/state-machine-testing-proptest/
[open]: https://blog.nikosbaxevanis.com/2025/02/10/scaling-with-madhouse-rs/

## Counterexamples

The examples are over-simplified from [leanVM][leanvm]: a size on the
wire, a memory whose cells are written once, and a program counter.
Each has a bug put there to be found; `lake exe examples` runs them.

[leanvm]: https://github.com/leanEthereum/leanVM

### A property

A size goes on the wire in two bytes, yet a memory has up to 2^30
words.

```lean
def encode (n : Nat) : List UInt8 :=
  [n.toUInt8, (n >>> 8).toUInt8]

def decode : List UInt8 → Option Nat
  | [a, b] => some (a.toNat + 256 * b.toNat)
  | _ => none

def sizeRoundTrips : Property Id := property do
  let n ← forAll (Gen.nat (.linear 0 (2 ^ 30)))
  tripping n encode decode
```

```
✗ size round trips failed after 2 tests and 16 shrinks.

  forAll 65536
  === failed
    lhs: some 0
    rhs: some 65536
```

### A state machine, transitions as one type

The model writes a cell once; this memory overwrites it.

```lean
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
```

```
✗ memory is write-once failed after 6 tests and 5 shrinks.

  forAll ([], [Op.set 0 0, Op.set 0 1])
  === failed
    lhs: 1
    rhs: 0
```

### A state machine, commands as types

Each instruction is a type of its own, and nothing lists them all.

```lean
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
```

In the order given, a step and then a jump, the scenario passes.  With
`MADHOUSE=1` in the environment the same commands run in random
sequences:

```
✗ pc stays in the program failed after 18 tests and 1 shrink.

  forAll [JUMP(7), NEXT]
  executed JUMP(7)
  executed NEXT
  pc left the program
```

## Installation

In `lakefile.toml`, on Lean 4.35.0 or later:

```toml
[[require]]
name = "hedgehog"
git = "https://github.com/hedgehogqa/lean-hedgehog"
rev = "master"
```

The guide is `USAGE`.

## License

BSD-3-Clause, as Haskell Hedgehog; see `COPYING`.

## AI disclosure

lean-hedgehog was written with strong assistance from AI coding agents,
with humans leading the ideas.  This would not exist without
[Haskell Hedgehog][haskell], written by hand.

- [Write you some QuickCheck][wysq] (2016): notes from learning how
  such a library works.
- [Gens N' Roses: Appetite for Reduction][talk] (YOW! 2017): Jacob
  Stanley on the design.

[haskell]: https://github.com/hedgehogqa/haskell-hedgehog
[wysq]: https://blog.nikosbaxevanis.com/2016/02/08/write-you-some-quickcheck/
[talk]: https://www.youtube.com/watch?v=LfD0DHqpeVQ

## In memory of Jacob Stanley

lean-hedgehog is dedicated to Jacob Stanley, author and co-founder of
Hedgehog, who passed away on 9 April 2023.
