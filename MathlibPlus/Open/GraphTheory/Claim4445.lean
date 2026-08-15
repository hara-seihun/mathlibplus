import Mathlib

namespace MathlibPlus.Open.GraphTheory.Claim4445

/-- A simple edge is an unordered, non-diagonal pair of vertices. -/
def SimpleEdge (V : Type*) [DecidableEq V] := {e : Finset V // e.card = 2}

/-- The edge map induced by a permutation of the vertices. -/
def edgeMap {V : Type*} [DecidableEq V] (σ : Equiv.Perm V)
    (e : SimpleEdge V) : SimpleEdge V :=
  ⟨e.1.image σ, by
    simpa [e.2] using Finset.card_image_of_injective e.1 σ.injective⟩

/-- A fixed-point card cocycle assigns a vertex permutation to each deleted vertex. -/
structure FixedPointCardCocycle (V : Type*) [DecidableEq V] where
  map : V → Equiv.Perm V
  fixes : ∀ i : V, map i i = i

/-- The exact closure condition for a finite constraint component. -/
def closedConstraintComponent_claim4445
    {V : Type*} [DecidableEq V]
    (cocycle : FixedPointCardCocycle V)
    (A_c B_c : Finset (SimpleEdge V)) : Prop :=
  (∀ e ∈ A_c, ∀ i : V, i ∉ e.1 → edgeMap (cocycle.map i) e ∈ B_c) ∧
    (∀ f ∈ B_c, ∀ i : V, i ∉ f.1 → edgeMap (cocycle.map i).symm f ∈ A_c)

end MathlibPlus.Open.GraphTheory.Claim4445
