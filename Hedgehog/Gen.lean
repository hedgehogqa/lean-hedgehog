module

public import Hedgehog.Seed
public import Hedgehog.Tree
public import Hedgehog.Range

/-!
# Generators

A `Gen α` makes, from a size and a seed, a shrink tree of `α`.  There is
no separate shrinking function to write or to keep in step with the
generator: `map`, `bind`, `filter` and the collection generators act on
whole trees.

A value in the tree may be `none`: the generator discarded it (`discard`,
`filter`, a failed `guard`).  A discarded root makes the test runner try
again; a discarded shrink is skipped.

`Gen` is pure, and so is a test case: the same size and seed give the
same tree.  Haskell Hedgehog's `GenT m` puts a monad under the tree; an
inductive type in Lean cannot (the tree would not be strictly positive in
`m`), so effects belong to the test, not to the generator.
-/

@[expose] public section

namespace Hedgehog

/-- A generator of `α` with integrated shrinking. -/
structure Gen (α : Type) where
  run : Size → Seed → Tree (Option α)

namespace Gen

open Integral

variable {α β γ : Type}

/-- Generate nothing: the runner discards the test case. -/
def discard : Gen α :=
  ⟨fun _ _ => .singleton none⟩

protected def pure (x : α) : Gen α :=
  ⟨fun _ _ => .singleton (some x)⟩

protected def map (f : α → β) (g : Gen α) : Gen β :=
  ⟨fun size seed => (g.run size seed).map (Option.map f)⟩

/-- Run `g`, then the generator `k` makes from its value, on independent
seeds.  A shrink of `g` reruns `k` on the same seed. -/
protected def bind (g : Gen α) (k : α → Gen β) : Gen β :=
  ⟨fun size seed =>
    let (s1, s2) := seed.split
    (g.run size s1).bind fun
      | none => .singleton none
      | some x => (k x).run size s2⟩

instance : Inhabited (Gen α) :=
  ⟨discard⟩

instance : Monad Gen where
  pure := Gen.pure
  map := Gen.map
  bind := Gen.bind

/-- `failure` is `discard`; `g <|> h` is `h` when `g` discards. -/
instance : Alternative Gen where
  failure := discard
  orElse g h := ⟨fun size seed =>
    let (s1, s2) := seed.split
    let t := g.run size s1
    if t.value.isSome then t else (h ()).run size s2⟩

/-- Generate two values that do not depend on each other.  Prefer this to
`bind` where it applies: each side keeps shrinking after the other did. -/
def zipWith (f : α → β → γ) (g : Gen α) (h : Gen β) : Gen γ :=
  ⟨fun size seed =>
    let (s1, s2) := seed.split
    Tree.zipWith (fun x y => f <$> x <*> y) (g.run size s1) (h.run size s2)⟩

def zip (g : Gen α) (h : Gen β) : Gen (α × β) :=
  zipWith Prod.mk g h

/-! ## Size -/

/-- A generator that depends on the size. -/
def sized (f : Size → Gen α) : Gen α :=
  ⟨fun size seed => (f size).run size seed⟩

/-- Run `g` at the size `f` gives. -/
def scale (f : Size → Size) (g : Gen α) : Gen α :=
  ⟨fun size seed => g.run (f size) seed⟩

/-- Run `g` at a fixed size. -/
def resize (size : Size) (g : Gen α) : Gen α :=
  scale (fun _ => size) g

/-- The size times the golden ratio's inverse, about 0.618, rounded. -/
def golden (size : Size) : Size :=
  (size * 61803398875 * 2 + 100000000000) / 200000000000

/-- Run `g` at a smaller size; use it on recursive calls. -/
def small (g : Gen α) : Gen α :=
  scale golden g

/-! ## Shrinking -/

/-- Add the shrinks `f` gives to those `g` has. -/
def shrink (f : α → List α) (g : Gen α) : Gen α :=
  ⟨fun size seed => (g.run size seed).expand fun
    | some x => (f x).map some
    | none => []⟩

/-- Drop the shrinks of `g`. -/
def prune (g : Gen α) : Gen α :=
  ⟨fun size seed => (g.run size seed).prune 0⟩

/-! ## Numbers -/

/-- The shrink tree of a number: `top`, with a binary search between
`bottom` and `top` below it. -/
partial def binarySearchTree (bottom top : Int) : Tree Int :=
  let shrinks := Shrink.towards bottom top
  .node top (List.zipWith (fun b t _ => binarySearchTree b t)
    shrinks (shrinks.drop 1))

/-- A number in the range, uniformly, shrinking to the range's origin by
binary search. -/
def integral [Integral α] (range : Range α) : Gen α :=
  ⟨fun size seed =>
    let origin := toInt range.origin
    let lo := toInt (range.lowerBound size)
    let hi := toInt (range.upperBound size)
    let x := lo + ((seed.nextNat 0 (hi - lo).toNat).1 : Nat)
    let tree :=
      if x = origin then .singleton x
      else (binarySearchTree origin x).consChild origin
    tree.map fun n => some (ofInt n)⟩

def nat (range : Range Nat) : Gen Nat :=
  integral range

def int (range : Range Int) : Gen Int :=
  integral range

/-- `false` or `true`, shrinking to `false`. -/
def bool : Gen Bool :=
  (· != 0) <$> nat (.constant 0 1)

/-! ## Choice -/

/-- One of `xs`, shrinking to the first.  It discards when `xs` is
empty. -/
def element (xs : List α) : Gen α := do
  let i ← nat (.constant 0 (xs.length - 1))
  match xs[i]? with
  | some x => pure x
  | none => discard

/-- One of the generators, shrinking to the first.  It discards when
there is none. -/
def choice (gs : List (Gen α)) : Gen α := do
  let i ← nat (.constant 0 (gs.length - 1))
  gs[i]?.getD discard

/-- One of the generators, each chosen in proportion to its weight,
shrinking to the first. -/
def frequency (gs : List (Nat × Gen α)) : Gen α := do
  let total := gs.foldl (fun n g => n + g.1) 0
  let n ← nat (.constant 1 total)
  let rec pick : Nat → List (Nat × Gen α) → Gen α
    | _, [] => discard
    | n, (k, g) :: gs => if n ≤ k then g else pick (n - k) gs
  pick n gs

/-- A generator that is built when it runs.  Lean is strict, so a
generator that refers to itself must do so through `delay`. -/
def delay (f : Unit → Gen α) : Gen α :=
  ⟨fun size seed => (f ()).run size seed⟩

/-- Choose among `leaves` at size 1 or less, and among both lists
otherwise, with the generators of `nodes` run at a smaller size.  This is
what keeps a recursive generator finite; the recursive references in
`nodes` go through `delay`. -/
def recursive (f : List (Gen α) → Gen α) (leaves nodes : List (Gen α)) :
    Gen α :=
  sized fun size =>
    if size ≤ 1 then f leaves else f (leaves ++ nodes.map small)

/-- `none` now and then, less often as the size grows; shrinks to
`none`. -/
def option (g : Gen α) : Gen (Option α) :=
  sized fun size => frequency [(2, pure none), (1 + size, some <$> g)]

/-! ## Conditions -/

/-- The values of `g` that `f` keeps, mapped.  It tries `g` at growing
sizes up to a hundred times, then discards. -/
def filterMap (f : α → Option β) (g : Gen α) : Gen β :=
  ⟨fun size seed =>
    let rec attempt : Nat → Nat → Seed → Tree (Option β)
      | 0, _, _ => .singleton none
      | fuel + 1, k, seed =>
        let (s1, s2) := seed.split
        let t := g.run (2 * k + size) s1
        if (t.value.bind f).isSome then t.map (·.bind f)
        else attempt fuel (k + 1) s2
    attempt 100 0 seed⟩

/-- The values of `g` that satisfy `p`. -/
def filter (p : α → Bool) (g : Gen α) : Gen α :=
  filterMap (fun x => if p x then some x else none) g

/-! ## Collections -/

/-- The trees of `gs`, on independent seeds. -/
def trees (size : Size) : Seed → List (Gen α) → List (Tree (Option α))
  | _, [] => []
  | seed, g :: gs =>
    let (s1, s2) := seed.split
    g.run size s1 :: trees size s2 gs

/-- A value from each generator, in order.  It shrinks by removing
elements while at least `atLeast` stay, and by shrinking one element. -/
def sequence (gs : List (Gen α)) (atLeast : Nat := 0) : Gen (List α) :=
  ⟨fun size seed =>
    (Tree.interleave (trees size seed gs)).map fun xs => do
      let xs ← xs.mapM id
      if atLeast ≤ xs.length then some xs else none⟩

/-- A list with a length in the range. -/
def list (range : Range Nat) (g : Gen α) : Gen (List α) :=
  sized fun size => do
    let n ← prune (nat range)
    sequence (List.replicate n g) (range.lowerBound size)

def array (range : Range Nat) (g : Gen α) : Gen (Array α) :=
  List.toArray <$> list range g

/-- A sublist of `xs`, shrinking towards the empty list. -/
def subsequence (xs : List α) : Gen (List α) :=
  shrink Shrink.list (xs.filterM fun _ => bool)

/-- A permutation of `xs`, shrinking towards `xs` itself. -/
def shuffle (xs : List α) : Gen (List α) :=
  let rec go : Nat → List α → Gen (List α)
    | 0, _ => pure []
    | n + 1, xs => do
      let i ← nat (.constant 0 n)
      match xs[i]? with
      | some x => (x :: ·) <$> go n (xs.eraseIdx i)
      | none => pure []
  go xs.length xs

/-! ## Characters and strings -/

def char (range : Range Char) : Gen Char :=
  integral range

def lower : Gen Char := char (.constant 'a' 'z')
def upper : Gen Char := char (.constant 'A' 'Z')
def digit : Gen Char := char (.constant '0' '9')
def alpha : Gen Char := choice [lower, upper]
def alphaNum : Gen Char := choice [lower, upper, digit]

/-- An ASCII character, `'\x00'` to `'\x7f'`. -/
def ascii : Gen Char := char (.constant '\x00' '\x7f')

/-- A Unicode scalar value, shrinking to `'a'`. -/
def unicode : Gen Char :=
  filterMap
    (fun n => if h : n.isValidChar then some ⟨n, h⟩ else none)
    (integral (.constantFrom 97 0 0x10ffff))

def string (range : Range Nat) (g : Gen Char) : Gen String :=
  String.ofList <$> list range g

/-- A byte array with a length in the range; it shrinks as a list of
bytes does, by losing bytes and towards zeros. -/
def bytes (range : Range Nat) : Gen ByteArray :=
  (fun bs => ByteArray.mk bs.toArray)
    <$> list range (integral (.constant (0 : UInt8) 255))

/-! ## Looking at a generator -/

/-- A value of `g` at a size, 30 unless given. -/
def sample (g : Gen α) (size : Size := 30) : IO α := do
  let rec attempt : Nat → Seed → IO α
    | 0, _ => throw (IO.userError "Gen.sample: too many discards")
    | fuel + 1, seed =>
      let (s1, s2) := seed.split
      match (g.run size s1).value with
      | some x => pure x
      | none => attempt fuel s2
  attempt 100 (← Seed.random)

/-- The shrink tree of `g` at a size and seed, down to `depth`. -/
def render [Repr α] (g : Gen α) (size : Size) (seed : Seed)
    (depth : Nat := 2) : String :=
  let t := (g.run size seed).map fun
    | some x => reprStr x
    | none => "<discard>"
  t.render depth

end Gen
end Hedgehog
