module

public import Hedgehog.Property

/-!
# Model-based testing: transitions as one type

The first of two ways to test a stateful system against a model, after
Rust's proptest-state-machine.  A `Model` is the reference: its state, a
generator of the transitions possible in a state, and what a transition
does to the state.  A `StateMachine` adds the system under test and how
each transition acts on it.

All transitions are values of one type `τ`, usually an inductive type
with a constructor for each operation, and one `apply` matches on it.
This is the closed side of the expression problem: a new operation edits
the type and each function over it, and Lean checks that none is missed.
`Hedgehog.Command` is the open side.

A sequence shrinks by removing transitions and by shrinking each one;
shrinks in which a precondition no longer holds are dropped.
-/

@[expose] public section

namespace Hedgehog

/-- The reference state machine: a pure model of the system. -/
structure Model (σ τ : Type) where
  /-- The state to start from. -/
  initState : Gen σ
  /-- The transitions to choose from in a state. -/
  transitions : σ → Gen τ
  /-- The state after a transition. -/
  apply : σ → τ → σ
  /-- Whether a transition may run in a state.  `transitions` may respect
  it already; shrinking removes earlier transitions, so it is checked
  again on every shrunk sequence. -/
  preconditions : σ → τ → Bool := fun _ _ => true

namespace Model

variable {σ τ : Type}

/-- Whether each precondition holds in the state its transition meets. -/
def valid (model : Model σ τ) : σ → List τ → Bool
  | _, [] => true
  | s, t :: ts => model.preconditions s t && valid model (model.apply s t) ts

/-- The trees of up to `n` transitions, each generated in the state the
ones before it lead to. -/
def trees (model : Model σ τ) (size : Size) :
    (n : Nat) → σ → Seed → List (Tree (Option τ))
  | 0, _, _ => []
  | n + 1, s, seed =>
    let (s1, s2) := seed.split
    let g := (model.transitions s).filter (model.preconditions s)
    let t := g.run size s1
    match t.value with
    | some x => t :: trees model size n (model.apply s x) s2
    | none => []

/-- An initial state and a valid sequence of transitions from it, of a
length in the range or shorter. -/
def sequence (model : Model σ τ) (range : Range Nat) : Gen (σ × List τ) := do
  let s ← model.initState
  let n ← Gen.prune (Gen.nat range)
  let transitions : Gen (List τ) := ⟨fun size seed =>
    (Tree.interleave (model.trees size n s seed)).map fun ts => do
      let ts ← ts.mapM id
      if model.valid s ts then some ts else none⟩
  pure (s, ← transitions)

end Model

/-- A model and the system under test, of type `ς`, with effects in
`m`. -/
structure StateMachine (σ τ ς : Type) (m : Type → Type) [Monad m]
    extends Model σ τ where
  /-- The system for an initial model state. -/
  initSut : σ → m ς
  /-- Run a transition on the system, given the model state before the
  transition and the one after it. -/
  applySut : ς → σ → σ → τ → TestT m ς
  /-- What must hold after every transition. -/
  invariants : ς → σ → TestT m Unit := fun _ _ => pure ()
  /-- Release the system after a sequence that passed. -/
  teardown : ς → m Unit := fun _ => pure ()

namespace StateMachine

variable {σ τ ς : Type} {m : Type → Type} [Monad m]

/-- Run the transitions on the model and the system, side by side. -/
def run (sm : StateMachine σ τ ς m) (s : σ) (ts : List τ) :
    TestT m Unit := do
  let mut s := s
  let mut sut ← liftM (sm.initSut s)
  sm.invariants sut s
  for t in ts do
    let before := s
    s := sm.apply s t
    sut ← sm.applySut sut before s t
    sm.invariants sut s
  liftM (sm.teardown sut)

/-- The system agrees with the model on every sequence of transitions. -/
def property [Repr σ] [Repr τ] (sm : StateMachine σ τ ς m)
    (range : Range Nat := .linear 1 50) : Property m :=
  propertyM do
    let (s, ts) ← forAll (sm.toModel.sequence range)
    pure (sm.run s ts)

end StateMachine
end Hedgehog
