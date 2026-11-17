module

public import Hedgehog.Shrink

/-!
# Shrink trees

A generator in Hedgehog makes a `Tree`, not a value: the value at the root
and, below it, the smaller values to try when a test fails.  Mapping and
binding generators maps and binds their trees, so shrinks are composed
with the generators and obey whatever invariants the generators set up.
This is integrated shrinking.

Haskell gets a lazy tree from the language.  Here children are suspended
explicitly, and `Tree` stays an ordinary inductive type: `map` and `bind`
are total, and the functor and monad laws are theorems (`LawfulMonad
Tree`), not tests.
-/

@[expose] public section

namespace Hedgehog

/-- A value and the smaller values to try in its place, each with shrinks
of its own.  A child is computed when it is applied to `()`. -/
inductive Tree (α : Type) where
  | node (value : α) (children : List (Unit → Tree α))

namespace Tree

variable {α β γ : Type}

def value : Tree α → α
  | node x _ => x

def children : Tree α → List (Unit → Tree α)
  | node _ xs => xs

/-- A value that does not shrink. -/
def singleton (x : α) : Tree α :=
  node x []

instance [Nonempty α] : Nonempty (Tree α) :=
  ‹Nonempty α›.elim fun x => ⟨singleton x⟩

instance [Inhabited α] : Inhabited (Tree α) :=
  ⟨singleton default⟩

mutual
def map (f : α → β) : Tree α → Tree β
  | node x xs => node (f x) (mapForest f xs)

def mapForest (f : α → β) : List (Unit → Tree α) → List (Unit → Tree β)
  | [] => []
  | t :: ts => (fun u => map f (t u)) :: mapForest f ts
end

mutual
/-- Replace each value by a tree.  The shrinks of the outer value come
first, each rebuilding the inner tree, then the shrinks of the inner
one. -/
def bind (k : α → Tree β) : Tree α → Tree β
  | node x xs =>
    match k x with
    | node y ys => node y (bindForest k xs ++ ys)

def bindForest (k : α → Tree β) : List (Unit → Tree α) → List (Unit → Tree β)
  | [] => []
  | t :: ts => (fun u => bind k (t u)) :: bindForest k ts
end

instance : Monad Tree where
  pure := singleton
  map := Tree.map
  bind t k := Tree.bind k t

/-- The tree of `x` whose shrinks are `f x`, each shrinking by `f` again.
It is `partial` because nothing makes `f` stop. -/
partial def unfold (f : α → List α) (x : α) : Tree α :=
  node x ((f x).map fun y _ => unfold f y)

/-- The children of `unfold f x`. -/
def unfoldForest (f : α → List α) (x : α) : List (Unit → Tree α) :=
  (f x).map fun y _ => unfold f y

mutual
/-- Add the shrinks `f` gives, at every node, after the ones present. -/
def expand (f : α → List α) : Tree α → Tree α
  | node x xs => node x (expandForest f xs ++ unfoldForest f x)

def expandForest (f : α → List α) : List (Unit → Tree α) → List (Unit → Tree α)
  | [] => []
  | t :: ts => (fun u => expand f (t u)) :: expandForest f ts
end

/-- Cut the tree below `depth`; `prune 0` leaves a value with no shrinks. -/
def prune : (depth : Nat) → Tree α → Tree α
  | 0, node x _ => node x []
  | n + 1, node x xs => node x (xs.map fun t _ => prune n (t ()))

/-- Add `x` as the first shrink. -/
def consChild (x : α) : Tree α → Tree α
  | node y ys => node y ((fun _ => singleton x) :: ys)

/-- The shrinks of `zipWith`. -/
partial def zipForest (f : α → β → γ) (l : Tree α) (r : Tree β) :
    List (Unit → Tree γ) :=
  let left := l.children.map fun t _ =>
    let l := t ()
    node (f l.value r.value) (zipForest f l r)
  let right := r.children.map fun t _ =>
    let r := t ()
    node (f l.value r.value) (zipForest f l r)
  left ++ right

/-- Combine two trees that do not depend on each other.  Unlike `bind`,
shrinking one side keeps the other, and both stay shrinkable. -/
def zipWith (f : α → β → γ) (l : Tree α) (r : Tree β) : Tree γ :=
  node (f l.value r.value) (zipForest f l r)

/-- A tree of lists from a list of trees.  It shrinks first by removing
elements (`Shrink.list`), then by shrinking one element. -/
partial def interleave (ts : List (Tree α)) : Tree (List α) :=
  let n := ts.length
  let drops := (Shrink.halves n).flatMap fun k =>
    (List.range (n / k)).map fun i (_ : Unit) =>
      interleave (ts.take (i * k) ++ ts.drop ((i + 1) * k))
  let shrinks := (List.range n).flatMap fun i =>
    match ts[i]? with
    | some t => t.children.map fun c (_ : Unit) => interleave (ts.set i (c ()))
    | none => []
  node (ts.map value) (drops ++ shrinks)

/-- The lines of `render`. -/
def lines : (depth : Nat) → Tree String → List String
  | 0, node x _ => [x]
  | n + 1, node x xs =>
    x :: xs.flatMap fun t => (lines n (t ())).map ("  " ++ ·)

/-- The tree down to `depth`, a value per line, shrinks indented. -/
def render (depth : Nat) (t : Tree String) : String :=
  "\n".intercalate (lines depth t)

/-! ## Laws -/

mutual
theorem map_id : (t : Tree α) → map id t = t
  | node x xs => by simp [map, mapForest_id xs]

theorem mapForest_id : (ts : List (Unit → Tree α)) → mapForest id ts = ts
  | [] => rfl
  | t :: ts => by
    simp only [mapForest, mapForest_id ts]
    congr 1; funext u; exact map_id (t u)
end

theorem bindForest_append (k : α → Tree β) :
    (ts us : List (Unit → Tree α)) →
      bindForest k (ts ++ us) = bindForest k ts ++ bindForest k us
  | [], _ => rfl
  | t :: ts, us => by simp [bindForest, bindForest_append k ts us]

theorem singleton_bind (x : α) (k : α → Tree β) :
    bind k (singleton x) = k x := by
  cases h : k x
  simp [singleton, bind, bindForest, h]

mutual
theorem bind_singleton : (t : Tree α) → bind singleton t = t
  | node x xs => by simp [bind, singleton, bindForest_singleton xs]

theorem bindForest_singleton :
    (ts : List (Unit → Tree α)) → bindForest singleton ts = ts
  | [] => rfl
  | t :: ts => by
    simp only [bindForest, bindForest_singleton ts]
    congr 1; funext u; exact bind_singleton (t u)
end

mutual
theorem bind_assoc (f : α → Tree β) (g : β → Tree γ) :
    (t : Tree α) → bind g (bind f t) = bind (fun x => bind g (f x)) t
  | node x xs => by
    cases hf : f x with
    | node y ys =>
      cases hg : g y with
      | node z zs =>
        simp [bind, hf, hg, bindForest_append, bindForest_assoc f g xs]

theorem bindForest_assoc (f : α → Tree β) (g : β → Tree γ) :
    (ts : List (Unit → Tree α)) →
      bindForest g (bindForest f ts) =
        bindForest (fun x => bind g (f x)) ts
  | [] => rfl
  | t :: ts => by
    simp only [bindForest, bindForest_assoc f g ts]
    congr 1; funext u; exact bind_assoc f g (t u)
end

mutual
theorem bind_singleton_comp (f : α → β) :
    (t : Tree α) → bind (fun x => singleton (f x)) t = map f t
  | node x xs => by
    simp [bind, map, singleton, ← bindForest_singleton_comp f xs]

theorem bindForest_singleton_comp (f : α → β) :
    (ts : List (Unit → Tree α)) →
      bindForest (fun x => singleton (f x)) ts = mapForest f ts
  | [] => rfl
  | t :: ts => by
    simp only [bindForest, mapForest, bindForest_singleton_comp f ts]
    congr 1; funext u; exact bind_singleton_comp f (t u)
end

/-- `Tree` is a lawful monad: Haskell Hedgehog tests these laws, Lean
proves them. -/
instance : LawfulMonad Tree :=
  LawfulMonad.mk'
    (id_map := map_id)
    (pure_bind := singleton_bind)
    (bind_assoc := fun t f g => bind_assoc f g t)
    (bind_pure_comp := fun f t => bind_singleton_comp f t)

end Tree
end Hedgehog
