module

/-!
# Splittable random seeds

SplitMix64, as in Haskell Hedgehog.  A seed splits into two independent
seeds, so each generator in a composition draws from a stream of its own
and a test case is a pure function of one seed and one size.
-/

@[expose] public section

namespace Hedgehog

/-- A SplitMix64 state.  `gamma` is odd. -/
structure Seed where
  value : UInt64
  gamma : UInt64
  deriving Repr, BEq, Inhabited

namespace Seed

/-- An odd approximation of `2^64 / φ`. -/
def goldenGamma : UInt64 := 0x9e3779b97f4a7c15

def mix64 (x : UInt64) : UInt64 :=
  let y := (x ^^^ (x >>> 33)) * 0xff51afd7ed558ccd
  let z := (y ^^^ (y >>> 33)) * 0xc4ceb9fe1a85ec53
  z ^^^ (z >>> 33)

def mix64variant13 (x : UInt64) : UInt64 :=
  let y := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (y ^^^ (y >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- The number of set bits. -/
def popCount (x : UInt64) : Nat :=
  (List.range 64).foldl (fun n i => n + ((x >>> i.toUInt64) &&& 1).toNat) 0

/-- An odd gamma with enough bit transitions to mix well. -/
def mixGamma (x : UInt64) : UInt64 :=
  let y := mix64variant13 x ||| 1
  if popCount (y ^^^ (y >>> 1)) < 24 then y ^^^ 0xaaaaaaaaaaaaaaaa else y

/-- The seed for a number: the same number gives the same seed. -/
def ofNat (n : Nat) : Seed :=
  let x := n.toUInt64
  ⟨mix64 x, mixGamma (x + goldenGamma)⟩

def next (s : Seed) : UInt64 × Seed :=
  let v := s.value + s.gamma
  (v, { s with value := v })

/-- A uniform 64-bit word and the seed to continue with. -/
def nextUInt64 (s : Seed) : UInt64 × Seed :=
  let (v, s) := s.next
  (mix64 v, s)

/-- Two independent seeds. -/
def split (s : Seed) : Seed × Seed :=
  let (v, s) := s.next
  let (g, s) := s.next
  (s, ⟨mix64 v, mixGamma g⟩)

/-- A number between `lo` and `hi`, both included, in either order.  It
draws 64 bits more than the bounds need, so the bias of the final
reduction is below `2^-64`. -/
def nextNat (lo hi : Nat) (s : Seed) : Nat × Seed :=
  let (lo, hi) := if lo ≤ hi then (lo, hi) else (hi, lo)
  let k := hi - lo + 1
  let (n, s) := (List.range (k.log2 / 64 + 2)).foldl
    (fun (n, s) _ => let (w, s) := s.nextUInt64; (n * 2 ^ 64 + w.toNat, s))
    (0, s)
  (lo + n % k, s)

/-- A seed from the system's entropy. -/
def random : IO Seed := do
  let bytes ← IO.getRandomBytes 8
  pure (ofNat (bytes.foldl (fun n b => n * 256 + b.toNat) 0))

end Seed
end Hedgehog
