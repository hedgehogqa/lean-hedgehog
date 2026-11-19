import HedgehogTest.Basic

/-!
Each generator and each piece under it: seeds, ranges, trees.  Facts
are checked on two hundred seeds; false properties must shrink to the
counterexample named.
-/

namespace HedgehogTest.Generators

open Hedgehog
open HedgehogTest.Basic (shrinksTo)

/-- The root values of `g` on two hundred seeds. -/
def draws {α : Type} (g : Gen α) (size : Size := 50) : List (Option α) :=
  (List.range 200).map fun i => (g.run size (Seed.ofNat i)).value

/-- Whether `g` never discards and every value satisfies `p`. -/
def always {α : Type} (g : Gen α) (p : α → Bool) (size : Size := 50) :
    Bool :=
  (draws g size).all fun x => x.any p

/-- Whether `g` discards on every seed. -/
def discards {α : Type} (g : Gen α) : Bool :=
  (draws g).all Option.isNone

/-- How many of the two hundred values satisfy `p`. -/
def countWhere {α : Type} (g : Gen α) (p : α → Bool) : Nat :=
  (draws g).countP fun x => x.any p

/-- A property that fails on every value of `g`. -/
def never {α : Type} [Repr α] (g : Gen α) : Property Id := property do
  let _ ← forAll g
  failure

inductive Expr where
  | lit (n : Nat)
  | add (a b : Expr)
  deriving Repr

def Expr.depth : Expr → Nat
  | .lit _ => 0
  | .add a b => max a.depth b.depth + 1

partial def genExpr (_ : Unit) : Gen Expr :=
  Gen.recursive Gen.choice
    [Expr.lit <$> Gen.nat (.linear 0 9)]
    [Gen.zipWith Expr.add (Gen.delay genExpr) (Gen.delay genExpr)]

def numbers : Tree Int :=
  Tree.unfold (Shrink.towards 0) 3

def seeds : List (String × Bool) := [
  ("popCount", Seed.popCount 0 == 0 && Seed.popCount 0xff == 8
    && Seed.popCount 0xffffffffffffffff == 64),
  ("gamma is odd", (List.range 200).all fun i =>
    (Seed.ofNat i).gamma % 2 == 1 && (Seed.ofNat i).split.2.gamma % 2 == 1),
  ("nextNat of one value", (List.range 200).all fun i =>
    ((Seed.ofNat i).nextNat 7 7).1 == 7),
  ("nextNat with bounds reversed", (List.range 200).all fun i =>
    let n := ((Seed.ofNat i).nextNat 9 3).1
    3 ≤ n && n ≤ 9),
  ("nextNat reaches both bounds",
    let ns := (List.range 200).map fun i => ((Seed.ofNat i).nextNat 0 3).1
    ns.contains 0 && ns.contains 3),
  ("nextNat advances the seed",
    let s := Seed.ofNat 1
    (s.nextNat 0 1000).2 != s),
  ("split halves differ from the seed", (List.range 200).all fun i =>
    let s := Seed.ofNat i
    s.split.1 != s && s.split.2 != s)]

def ranges : List (String × Bool) := [
  ("singleton", (Range.singleton (5 : Nat)).bounds 99 == (5, 5)
    && (Range.singleton (5 : Nat)).origin == 5),
  ("constant ignores the size", (List.range 100).all fun n =>
    (Range.constant (1 : Nat) 9).bounds n == (1, 9)),
  ("constantFrom origin", (Range.constantFrom (0 : Int) (-5) 5).origin == 0),
  ("linear origin", (Range.linear (3 : Nat) 9).origin == 3),
  ("linear stays in bounds", (List.range 200).all fun n =>
    let (x, y) := (Range.linear (3 : Nat) 9).bounds n
    x == 3 && 3 ≤ y && y ≤ 9),
  ("linear grows", (List.range 99).all fun n =>
    ((Range.linear (0 : Nat) 1000).bounds n).2
      ≤ ((Range.linear (0 : Nat) 1000).bounds (n + 1)).2),
  ("exponential grows", (List.range 99).all fun n =>
    ((Range.exponential (0 : Nat) 1000).bounds n).2
      ≤ ((Range.exponential (0 : Nat) 1000).bounds (n + 1)).2),
  ("exponential is below linear", (List.range 100).all fun n =>
    ((Range.exponential (0 : Nat) 1000).bounds n).2
      ≤ ((Range.linear (0 : Nat) 1000).bounds n).2),
  ("exponential is exact at 2 ^ 256",
    (Range.exponential (0 : Nat) (2 ^ 256)).bounds 99 == (0, 2 ^ 256)),
  ("bounds in either order",
    let r := Range.constant (9 : Nat) 1
    r.lowerBound 0 == 1 && r.upperBound 0 == 9),
  ("map", ((· + 1) <$> Range.constant (1 : Nat) 9).bounds 0 == (2, 10)
    && ((· + 1) <$> Range.constant (1 : Nat) 9).origin == 2),
  ("clamp", Range.clamp 0 10 (-5) == 0 && Range.clamp 0 10 15 == 10
    && Range.clamp 10 0 15 == 10 && Range.clamp 0 10 5 == 5),
  ("Fin", (Range.linear (0 : Fin 8) 7).bounds 99 == (0, 7)),
  ("UInt8", (Range.linear (0 : UInt8) 255).bounds 99 == (0, 255)),
  ("Char", (Range.constant 'a' 'z').bounds 0 == ('a', 'z'))]

def trees : List (String × Bool) := [
  ("unfold", numbers.value == 3
    && numbers.children.map (fun t => (t ()).value) == [0, 2]),
  ("prune 0", (numbers.prune 0).children.isEmpty),
  ("prune 1", ((numbers.prune 1).children.map fun t => (t ()).children.length)
    == [0, 0]),
  ("consChild", ((Tree.singleton 5).consChild 1).children.map
    (fun t => (t ()).value) == [1]),
  ("expand", (((Tree.singleton 2).expand fun n =>
    if n > 0 then [n - 1] else []).map toString).render 5
      == "2\n  1\n    0"),
  ("render", (numbers.map toString).render 1 == "3\n  0\n  2"),
  ("map", (numbers.map (· + 1)).children.map (fun t => (t ()).value)
    == [1, 3]),
  ("bind", (numbers.bind fun n => Tree.node n [fun _ => .singleton 9]
    ).children.map (fun t => (t ()).value) == [0, 2, 9]),
  ("do notation", (do
    let x ← numbers
    let y ← Tree.singleton 10
    pure (x + y) : Tree Int).value == 13),
  ("zipWith", let t := Tree.zipWith (· + ·) numbers numbers
    t.value == 6 && t.children.map (fun t => (t ()).value) == [3, 5, 3, 5]),
  ("interleave", let t := Tree.interleave [numbers, numbers]
    t.value == [3, 3] && (t.children.map fun t => (t ()).value)
      == [[], [3], [3], [0, 3], [2, 3], [3, 0], [3, 2]])]

def generators : List (String × Bool) := [
  ("pure", always (pure 7 : Gen Nat) (· == 7)),
  ("discard", discards (Gen.discard : Gen Nat)),
  ("map", always ((· * 2) <$> Gen.nat (.constant 0 9)) (· % 2 == 0)),
  ("bool gives both", countWhere Gen.bool id > 50
    && countWhere Gen.bool (!·) > 50),
  ("nat reaches both bounds",
    countWhere (Gen.nat (.constant 0 3)) (· == 0) > 0
    && countWhere (Gen.nat (.constant 0 3)) (· == 3) > 0),
  ("int", always (Gen.int (.constant (-5) 5)) fun n => -5 ≤ n && n ≤ 5),
  ("Fin", always (Gen.integral (.constant (2 : Fin 8) 5)) fun i =>
    2 ≤ i.val && i.val ≤ 5),
  ("UInt8", always (Gen.integral (.constant (250 : UInt8) 255))
    (· ≥ 250)),
  ("UInt64", always (Gen.integral (.constant (0 : UInt64) (0 - 1)))
    fun _ => true),
  ("element", always (Gen.element [1, 2, 3]) [1, 2, 3].contains),
  ("element of nothing", discards (Gen.element ([] : List Nat))),
  ("choice", always (Gen.choice [pure 1, pure 2]) [1, 2].contains),
  ("choice of nothing", discards (Gen.choice ([] : List (Gen Nat)))),
  ("frequency skips weight zero",
    always (Gen.frequency [(0, pure 1), (1, pure 2)]) (· == 2)),
  ("frequency follows the weights",
    let n := countWhere (Gen.frequency [(1, pure 1), (9, pure 2)]) (· == 2)
    150 ≤ n && n < 200),
  ("frequency of nothing",
    discards (Gen.frequency ([] : List (Nat × Gen Nat)))),
  ("option gives both", countWhere (Gen.option Gen.bool) Option.isNone > 0
    && countWhere (Gen.option Gen.bool) Option.isSome > 100),
  ("orElse keeps the first", always (pure 2 <|> pure 1 : Gen Nat) (· == 2)),
  ("orElse replaces a discard",
    always (Gen.discard <|> pure 1 : Gen Nat) (· == 1)),
  ("filter", always (Gen.filter (· > 90) (Gen.nat (.constant 0 100)))
    (· > 90)),
  ("filter of nothing", discards (Gen.filter (fun _ => false) Gen.bool)),
  ("filterMap", always (Gen.filterMap
    (fun n => if n % 2 == 0 then some (n / 2) else none)
    (Gen.nat (.constant 0 100))) (· ≤ 50)),
  ("sized", always (Gen.sized pure) (· == 50)),
  ("resize", always (Gen.resize 42 (Gen.sized pure)) (· == 42)),
  ("scale", always (Gen.scale (· + 1) (Gen.sized pure)) (· == 51)),
  ("golden", Gen.golden 100 == 62 && Gen.golden 0 == 0 && Gen.golden 1 == 1),
  ("small", always (Gen.small (Gen.sized pure)) (· == 31)),
  ("prune", (List.range 200).all fun i =>
    ((Gen.prune (Gen.nat (.constant 0 100))).run 50
      (Seed.ofNat i)).children.isEmpty),
  ("shrink", (List.range 200).all fun i =>
    ((Gen.shrink (fun _ => [7]) (pure 1 : Gen Nat)).run 50
      (Seed.ofNat i)).children.map (fun t => (t ()).value) == [some 7]),
  ("sequence", always (Gen.sequence [pure 1, pure 2, pure 3])
    (· == [1, 2, 3])),
  ("sequence with a discard",
    discards (Gen.sequence [pure 1, Gen.discard, pure 3])),
  ("array", always (Gen.array (.constant 2 4) Gen.bool) fun xs =>
    2 ≤ xs.size && xs.size ≤ 4),
  ("string", always (Gen.string (.constant 2 4) Gen.digit) fun s =>
    2 ≤ s.length && s.length ≤ 4 && s.all Char.isDigit),
  ("bytes", always (Gen.bytes (.constant 2 4)) fun bs =>
    2 ≤ bs.size && bs.size ≤ 4),
  ("lower", always Gen.lower Char.isLower),
  ("upper", always Gen.upper Char.isUpper),
  ("digit", always Gen.digit Char.isDigit),
  ("alpha", always Gen.alpha Char.isAlpha),
  ("alphaNum", always Gen.alphaNum Char.isAlphanum),
  ("ascii", always Gen.ascii fun c => c.toNat < 128),
  ("unicode leaves the surrogates out", always Gen.unicode fun c =>
    c.toNat < 0xd800 || (0xdfff < c.toNat && c.toNat ≤ 0x10ffff)),
  ("unicode goes past ASCII",
    decide (countWhere Gen.unicode (·.toNat > 127) > 100)),
  ("recursive stops at size 1",
    always (genExpr ()) (·.depth == 0) (size := 1)),
  ("recursive recurses",
    ((draws (genExpr ()) 99).any fun e => e.any (·.depth > 1))),
  ("recursive is finite at any size",
    always (genExpr ()) (·.depth < 50) (size := 99)),
  ("render", (Gen.int (.constant 0 10)).render 30 (Seed.ofNat 1) 1
    == "9\n  0\n  5\n  7\n  8"),
  ("render of a discard",
    (Gen.discard : Gen Nat).render 0 (Seed.ofNat 1) == "<discard>")]

/-- Whether the property fails on each of twenty seeds with shrunk
inputs that satisfy `p`.  For shrinks with more than one end: a filter
can stop above the least value it allows, since the binary search only
steps on values it keeps; and after `bind`, a shrink of the first value
draws the second again, so the first stops where the second would no
longer fail. -/
def shrunk (property : Property Id) (p : List String → Bool) : Bool :=
  (List.range 20).all fun i =>
    (Basic.inputs (property.report (Seed.ofNat i))).any p

def shrinking : List (String × Bool) := [
  ("nat shrinks to the lower bound",
    shrinksTo (never (Gen.nat (.linear 3 100))) [["3"]]),
  ("int shrinks to the origin",
    shrinksTo (never (Gen.int (.linearFrom 5 (-100) 100))) [["5"]]),
  ("bool shrinks to false", shrinksTo (never Gen.bool) [["false"]]),
  ("char shrinks to the lower bound", shrinksTo (never Gen.lower) [["'a'"]]),
  ("unicode shrinks to a", shrinksTo (never Gen.unicode) [["'a'"]]),
  ("element shrinks to the first",
    shrinksTo (never (Gen.element [7, 8, 9])) [["7"]]),
  ("choice shrinks to the first",
    shrinksTo (never (Gen.choice [pure 7, pure 8])) [["7"]]),
  ("frequency shrinks to the first",
    shrinksTo (never (Gen.frequency [(1, pure 7), (9, pure 8)])) [["7"]]),
  ("option shrinks to none",
    shrinksTo (never (Gen.option Gen.bool)) [["none"]]),
  ("some shrinks inside", shrinksTo (property do
    let x ← forAll (Gen.option (Gen.nat (.linear 0 100)))
    ensure x.isNone) [["some 0"]]),
  ("list shrinks to the shortest allowed",
    shrinksTo (never (Gen.list (.constant 3 10) (Gen.nat (.linear 0 9))))
      [["[0, 0, 0]"]]),
  ("list shrinks to empty",
    shrinksTo (never (Gen.list (.linear 0 10) Gen.bool)) [["[]"]]),
  ("string shrinks", shrinksTo (property do
    let s ← forAll (Gen.string (.linear 0 20) Gen.lower)
    ensure (s.length < 2)) [["\"aa\""]]),
  ("bytes shrink", shrinksTo (property do
    let bs ← forAllWith bytesHex (Gen.bytes (.linear 0 20))
    ensure (bs.size < 2)) [["0000"]]),
  ("array shrinks", shrinksTo (property do
    let xs ← forAll (Gen.array (.linear 0 20) (Gen.nat (.linear 0 9)))
    ensure (xs.size < 2)) [["#[0, 0]"]]),
  ("filter keeps its condition while shrinking", shrunk (never
    (Gen.filter (· % 2 == 1) (Gen.nat (.linear 0 100)))) fun
      | [n] => n.toNat?.any fun n => n % 2 == 1 && n < 10
      | _ => false),
  ("subsequence shrinks to empty",
    shrinksTo (never (Gen.subsequence [1, 2, 3])) [["[]"]]),
  ("shuffle shrinks to the list itself",
    shrinksTo (never (Gen.shuffle [1, 2, 3])) [["[1, 2, 3]"]]),
  ("bind shrinks the second part to the bound", shrunk (property do
    let n ← forAll (Gen.nat (.linear 0 100))
    let m ← forAll (Gen.nat (.linear n (n + 100)))
    ensure (m < 10)) fun
      | [n, m] => m == "10" && n.toNat?.any (· ≤ 10)
      | _ => false),
  ("recursive shrinks to a leaf", shrinksTo (property do
    let e ← forAllWith (fun e => toString e.depth) (genExpr ())
    ensure (e.depth > 100)) [["0"]])]

end HedgehogTest.Generators
