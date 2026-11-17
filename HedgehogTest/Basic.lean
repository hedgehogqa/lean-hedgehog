import Hedgehog

/-!
Properties of the library, checked with the library, and fixed points of
the shrinking functions taken from Haskell Hedgehog's documentation.
-/

namespace HedgehogTest.Basic

open Hedgehog

/-- Facts with no generator involved. -/
def units : List (String × Bool) := [
  ("halves 15", Shrink.halves 15 == [15, 7, 3, 1]),
  ("towards 0 100", Shrink.towards 0 100 == [0, 50, 75, 88, 94, 97, 99]),
  ("towards 500 1000", Shrink.towards 500 1000 ==
    [500, 750, 875, 938, 969, 985, 993, 997, 999]),
  ("towards -50 -26", Shrink.towards (-50) (-26) == [-50, -38, -32, -29, -27]),
  ("towards x x", Shrink.towards 7 7 == []),
  ("removes 2", Shrink.removes 2 [1, 2, 3, 4, 5] == [[3, 4, 5], [1, 2, 5]]),
  ("list abcd", (Shrink.list "abcd".toList).map String.ofList ==
    ["", "cd", "ab", "bcd", "acd", "abd", "abc"]),
  ("linear at 0", (Range.linear (0 : Nat) 10000).bounds 0 == (0, 0)),
  ("linear at 50", (Range.linear (0 : Nat) 10000).bounds 50 == (0, 5050)),
  ("linear at 99", (Range.linear (0 : Nat) 10000).bounds 99 == (0, 10000)),
  ("linearFrom at 50",
    (Range.linearFrom (0 : Int) (-10) 20).bounds 50 == (-5, 10)),
  ("exponential at 0", (Range.exponential (1 : Nat) 512).bounds 0 == (1, 1)),
  ("exponential at 99",
    (Range.exponential (1 : Nat) 512).bounds 99 == (1, 512)),
  ("exponentialFrom at 99",
    (Range.exponentialFrom (0 : Int) (-128) 512).bounds 99 == (-128, 512)),
  ("split differs", let (a, b) := (Seed.ofNat 1).split; a != b),
  ("seeds repeat",
    (Seed.ofNat 1).nextNat 0 1000 == (Seed.ofNat 1).nextNat 0 1000)]

def reverseReverse : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 100) Gen.alpha)
  xs.reverse.reverse === xs

def integralInBounds : Property Id := property do
  let lo ← forAll (Gen.int (.linearFrom 0 (-1000) 1000))
  let hi ← forAll (Gen.int (.linear lo (lo + 1000)))
  let x ← forAll (Gen.int (.constant lo hi))
  ensure (lo ≤ x && x ≤ hi)

def listLengthInRange : Property Id := property do
  let lo ← forAll (Gen.nat (.linear 0 10))
  let hi ← forAll (Gen.nat (.linear lo (lo + 10)))
  let xs ← forAll (Gen.list (.constant lo hi) Gen.bool)
  ensure (lo ≤ xs.length && xs.length ≤ hi)

def towardsIsBetween : Property Id := property do
  let d ← forAll (Gen.int (.linearFrom 0 (-1000) 1000))
  let x ← forAll (Gen.int (.linearFrom 0 (-1000) 1000))
  let ys := Shrink.towards d x
  ensure (ys.all fun y => y != x && min d x ≤ y && y ≤ max d x)
  ensure (d == x || ys.head? == some d)

def nextNatInBounds : Property Id := property do
  let lo ← forAll (Gen.nat (.exponential 0 (2 ^ 80)))
  let hi ← forAll (Gen.nat (.exponential lo (2 ^ 80)))
  let seed ← forAll (Gen.nat (.linear 0 1000))
  let n := ((Seed.ofNat seed).nextNat lo hi).1
  ensure (lo ≤ n && n ≤ hi)

def natRoundTrip : Property Id := property do
  let n ← forAll (Gen.nat (.exponential 0 (2 ^ 64)))
  tripping n toString String.toNat?

def shuffleIsPermutation : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 20) (Gen.nat (.linear 0 9)))
  let ys ← forAll (Gen.shuffle xs)
  xs.mergeSort === ys.mergeSort

def subsequenceIsSublist : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 20) (Gen.nat (.linear 0 9)))
  let ys ← forAll (Gen.subsequence xs)
  ensure (ys.isSublist xs)

def filterHolds : Property Id := property do
  let n ← forAll (Gen.filter (· % 2 == 0) (Gen.nat (.linear 0 100)))
  n % 2 === 0

/-- An effect in the test, not in the generator. -/
def refHoldsWhatWasSet : Property IO := propertyM do
  let n ← forAll (Gen.nat (.linear 0 100))
  pure do
    let r ← IO.mkRef 0
    r.set n
    (← r.get) === n

def properties : List (String × Property Id) := [
  ("reverse reverse", reverseReverse),
  ("integral in bounds", integralInBounds),
  ("list length in range", listLengthInRange),
  ("towards is between", towardsIsBetween),
  ("nextNat in bounds", nextNatInBounds),
  ("nat round trip", natRoundTrip),
  ("shuffle is a permutation", shuffleIsPermutation),
  ("subsequence is a sublist", subsequenceIsSublist),
  ("filter holds", filterHolds)]

/-! Properties that are false, and what they must shrink to. -/

def reverseIsIdentity : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 100) (Gen.nat (.linear 0 1000)))
  xs.reverse === xs

def allBelow500 : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 100) (Gen.nat (.linear 0 1000)))
  ensure (xs.all (· < 500))

def notBothLarge : Property Id := property do
  let n := Gen.nat (.linear 0 100)
  let (x, y) ← forAll (Gen.zip n n)
  ensure (x < 30 || y < 30)

def alwaysDiscards : Property Id := property do
  let n ← forAll (Gen.nat (.linear 0 100))
  if n < 200 then discard
  failure

/-- The values `forAll` logged for the shrunk counterexample. -/
def inputs (r : Report) : Option (List String) :=
  match r.status with
  | .failed c => some (c.journal.toList.filterMap fun
    | .input value => some value
    | .note _ => none)
  | _ => none

/-- Whether the property fails on each of twenty seeds, shrunk to one of
the expected inputs. -/
def shrinksTo (p : Property Id) (expected : List (List String)) : Bool :=
  (List.range 20).all fun i =>
    match inputs (p.report (Seed.ofNat i)) with
    | some values => expected.contains values
    | none => false

/-- Whether a failure's size and seed reproduce it. -/
def rechecks (p : Property Id) : Bool :=
  match (p.report (Seed.ofNat 0)).status with
  | .failed c => (p.recheck c.size c.seed).status == .failed c
  | _ => false

def shrinking : List (String × Bool) := [
  ("reverse shrinks to two elements",
    shrinksTo reverseIsIdentity [["[0, 1]"], ["[1, 0]"]]),
  ("a bound shrinks to the bound", shrinksTo allBelow500 [["[500]"]]),
  ("both sides of zip shrink", shrinksTo notBothLarge [["(30, 30)"]]),
  ("recheck reproduces", rechecks reverseIsIdentity),
  ("reports repeat", (reverseIsIdentity.report (Seed.ofNat 3)).run ==
    (reverseIsIdentity.report (Seed.ofNat 3)).run),
  ("gives up", (alwaysDiscards.report (Seed.ofNat 0)).status == .gaveUp)]

end HedgehogTest.Basic
