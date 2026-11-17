module

/-!
# Shrinking steps

The lists of smaller candidates that shrink trees are built from.  Each
list starts with the most aggressive candidate, so a search that takes the
first failing one is a binary search.
-/

@[expose] public section

namespace Hedgehog.Shrink

/-- `n`, then its halves, down to `1`: `halves 15 = [15, 7, 3, 1]`. -/
def halves (n : Nat) : List Nat :=
  if n = 0 then [] else n :: halves (n / 2)
termination_by n
decreasing_by omega

/-- Candidates from `destination` up to, not including, `x`, by halving
the distance: `towards 0 100 = [0, 50, 75, 88, 94, 97, 99]`. -/
def towards (destination x : Int) : List Int :=
  if destination = x then []
  else
    let diff := x.tdiv 2 - destination.tdiv 2
    let steps := (halves diff.natAbs).map fun (h : Nat) => x - diff.sign * h
    match steps with
    | y :: _ => if destination = y then steps else destination :: steps
    | [] => [destination]

/-- `xs` with one run of `k` elements removed, for each of the consecutive
runs: `removes 2 [1, 2, 3, 4, 5] = [[3, 4, 5], [1, 2, 5]]`. -/
def removes {α : Type} (k : Nat) (xs : List α) : List (List α) :=
  if k = 0 then []
  else (List.range (xs.length / k)).map fun i =>
    xs.take (i * k) ++ xs.drop ((i + 1) * k)

/-- Sublists of `xs`, shortest first: all of it removed, then each half,
each quarter, and so on down to single elements. -/
def list {α : Type} (xs : List α) : List (List α) :=
  (halves xs.length).flatMap (removes · xs)

end Hedgehog.Shrink
