module

/-!
# Sizes and ranges

A test runs at a `Size` from 0 to 99, small first.  A `Range` gives the
bounds of a number or a length at each size, and the `origin` that
generated values shrink towards.
-/

@[expose] public section

namespace Hedgehog

/-- How large generated values may be, from 0 to 99. -/
abbrev Size := Nat

/-- Types that ranges and `Gen.integral` work on, through `Int`.  `ofInt`
is only applied to numbers within the bounds of a range. -/
class Integral (α : Type) where
  toInt : α → Int
  ofInt : Int → α

instance : Integral Int := ⟨id, id⟩
instance : Integral Nat := ⟨Int.ofNat, Int.toNat⟩
instance {n : Nat} : Integral (Fin (n + 1)) :=
  ⟨fun i => i.val, fun i => Fin.ofNat (n + 1) i.toNat⟩
instance : Integral UInt8 := ⟨fun x => x.toNat, fun i => .ofNat i.toNat⟩
instance : Integral UInt16 := ⟨fun x => x.toNat, fun i => .ofNat i.toNat⟩
instance : Integral UInt32 := ⟨fun x => x.toNat, fun i => .ofNat i.toNat⟩
instance : Integral UInt64 := ⟨fun x => x.toNat, fun i => .ofNat i.toNat⟩
instance : Integral Char := ⟨fun c => c.toNat, fun i => Char.ofNat i.toNat⟩

/-- Bounds that may depend on the size, and the value to shrink to. -/
structure Range (α : Type) where
  origin : α
  bounds : Size → α × α

namespace Range

open Integral

variable {α β : Type}

instance : Functor Range where
  map f r := ⟨f r.origin, fun n => let (x, y) := r.bounds n; (f x, f y)⟩

/-- The smaller bound at a size. -/
def lowerBound [Integral α] (r : Range α) (size : Size) : α :=
  let (x, y) := r.bounds size
  if toInt x ≤ toInt y then x else y

/-- The larger bound at a size. -/
def upperBound [Integral α] (r : Range α) (size : Size) : α :=
  let (x, y) := r.bounds size
  if toInt x ≤ toInt y then y else x

/-- Always `x`. -/
def singleton (x : α) : Range α :=
  ⟨x, fun _ => (x, x)⟩

/-- From `x` to `y` at every size, shrinking to `z`. -/
def constantFrom (z x y : α) : Range α :=
  ⟨z, fun _ => (x, y)⟩

/-- From `x` to `y` at every size, shrinking to `x`. -/
def constant (x y : α) : Range α :=
  constantFrom x x y

/-- `n`, kept between `x` and `y`. -/
def clamp (x y n : Int) : Int :=
  if x > y then min x (max y n) else min y (max x n)

/-- The point `size / 99` of the way from `z` to `n`. -/
def scaleLinear (size : Size) (z n : Int) : Int :=
  z + ((n - z) * (min size 99 : Nat)).tdiv 99

/-- Bounds that grow linearly with the size, from `z` at size 0 to `x`
and `y` at size 99, shrinking to `z`. -/
def linearFrom [Integral α] (z x y : α) : Range α :=
  ⟨z, fun size =>
    let (z, x, y) := (toInt z, toInt x, toInt y)
    (ofInt (clamp x y (scaleLinear size z x)),
     ofInt (clamp x y (scaleLinear size z y)))⟩

/-- From `x` to a bound that grows linearly to `y`, shrinking to `x`. -/
def linear [Integral α] (x y : α) : Range α :=
  linearFrom x x y

/-- The largest `r` from `lo` up to, not including, `hi` with `p r`, for
a `p` that holds at `lo` and, once false, stays false. -/
def search (p : Nat → Bool) : (fuel lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if p mid then search p fuel mid hi else search p fuel lo mid

/-- The point `size / 99` of the way from `z` to `n`, on a logarithmic
scale: the distance is `(|n - z| + 1) ^ (size / 99) - 1`, rounded down.
It is computed in integers, exactly, at any magnitude. -/
def scaleExponential (size : Size) (z n : Int) : Int :=
  let b := (n - z).natAbs + 1
  let target := b ^ min size 99
  let root := search (fun r => r ^ 99 ≤ target) (b.log2 + 2) 1 (b + 1)
  z + (n - z).sign * (root - 1 : Nat)

/-- Bounds that grow exponentially with the size, from `z` at size 0 to
`x` and `y` at size 99, shrinking to `z`. -/
def exponentialFrom [Integral α] (z x y : α) : Range α :=
  ⟨z, fun size =>
    let (z, x, y) := (toInt z, toInt x, toInt y)
    (ofInt (clamp x y (scaleExponential size z x)),
     ofInt (clamp x y (scaleExponential size z y)))⟩

/-- From `x` to a bound that grows exponentially to `y`, shrinking to
`x`. -/
def exponential [Integral α] (x y : α) : Range α :=
  exponentialFrom x x y

end Range
end Hedgehog
