import Mathlib

namespace MathlibPlus.Open.Combinatorics

universe u

private abbrev TwoSubset (V : Type u) := {e : Finset V // e.card = 2}

private def permTwoSubset {V : Type u} (π : Equiv.Perm V) (e : TwoSubset V) : TwoSubset V := by
  refine ⟨e.1.map π.toEmbedding, ?_⟩
  rw [Finset.card_map, e.2]

private def edgeConstraintHom {V : Type u} (π : V → Equiv.Perm V)
    (x y : Sum (TwoSubset V) (TwoSubset V)) : Type u := by
  classical
  exact match x, y with
  | Sum.inl e, Sum.inr f => {i : V // i ∉ e.1 ∧ permTwoSubset (π i) e = f}
  | _, _ => ULift.{u} Empty

/-- The bipartite multigraph whose arrows retain one edge for each local constraint. -/
def bipartiteEdgeConstraintMultigraph
    {V : Type u} [Fintype V] (n : ℕ)
    (π : V → Equiv.Perm V)
    (hV : Fintype.card V = n)
    (hπ : ∀ i : V, π i i = i) : Prop :=
  ∃ Γ : Quiver.{u, u} (Sum (TwoSubset V) (TwoSubset V)),
    ∀ x y, @Quiver.Hom _ Γ x y = edgeConstraintHom π x y

end MathlibPlus.Open.Combinatorics
