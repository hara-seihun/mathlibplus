import Mathlib

namespace MathlibPlus.Combinatorics.Claim27592

/-- Claim 27592: a proper packing cannot contain two blocks whose common
cardinality is strictly above half the ambient vertex set.  The source's
"connected" and "proper" conditions are represented explicitly; only the
pairwise-disjoint part of properness is needed for this cardinality bound. -/
theorem atMostOneLargeBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (blocks : Finset (Finset V)) (M : ℕ)
    (_hTree : G.IsTree)
    (hproper : Set.Pairwise (↑blocks : Set (Finset V)) Disjoint)
    (_hconnected : ∀ B ∈ blocks, (G.induce (B : Set V)).Connected)
    (_hupper : M < Fintype.card V)
    (hlower : Fintype.card V / 2 < M)
    (hsize : ∀ B ∈ blocks, B.card = M) :
    blocks.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro B hB C hC
  by_contra hne
  have hdis : Disjoint B C := hproper hB hC hne
  have hsub : B ∪ C ⊆ (Finset.univ : Finset V) := by
    intro x hx
    exact Finset.mem_univ x
  have hcard : (B ∪ C).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hsize B hB, hsize C hC] at hcard
  omega

end MathlibPlus.Combinatorics.Claim27592
