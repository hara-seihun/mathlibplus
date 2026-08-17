import Mathlib
import MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.TreeDegreeOneAnomaly

open scoped BigOperators
open MathlibPlus.Open.TreeSpectral

noncomputable section

/-- Claim 5961: the concrete one-vertex bottom of the graded tree carrier has
no leaf, while its one graft is the two-vertex tree with two leaf occurrences;
the resulting composition is twice, rather than once, the degree-one identity. -/
def degreeOneBottomAnomaly_claim5961 : Prop :=
  let K₁ : TreeClass 1 :=
    Quotient.mk (TreeGraphSetoid 1)
      (⟨⊥, SimpleGraph.IsTree.of_subsingleton⟩ : TreeGraph 1)
  let P₂ : TreeClass 2 :=
    Quotient.mk (TreeGraphSetoid 2)
      (⟨⊤, ⟨SimpleGraph.connected_top,
        SimpleGraph.IsAcyclic.of_card_le_two
          (((ENat.card_eq_coe_fintype_card (α := Fin 2)).trans
            (congrArg (fun n : ℕ => (n : ENat)) (Fintype.card_fin 2))).le)⟩⟩ :
        TreeGraph 2)
  (Quotient.out K₁).1 = (⊥ : SimpleGraph (Fin 1)) ∧
    (Quotient.out P₂).1 = (⊤ : SimpleGraph (Fin 2)) ∧
    (∀ v : Fin 1, ¬ IsLeaf (Quotient.out K₁).1 v) ∧
    graftBasis 1 K₁ = Finsupp.single P₂ (1 : ℚ) ∧
    Set.ncard {v : Fin 2 | IsLeaf (Quotient.out P₂).1 v} = 2 ∧
    leafDeletionBasis 2 P₂ = (2 : ℚ) • Finsupp.single K₁ (1 : ℚ) ∧
    (leafDeletion 2).comp (graft 1) =
      (2 : ℚ) • (LinearMap.id : TreeSpace 1 →ₗ[ℚ] TreeSpace 1) ∧
    (leafDeletion 2).comp (graft 1) ≠
      (1 : ℚ) • (LinearMap.id : TreeSpace 1 →ₗ[ℚ] TreeSpace 1)

end
end MathlibPlus.Open.ResearchFormalization.TreeDegreeOneAnomaly
