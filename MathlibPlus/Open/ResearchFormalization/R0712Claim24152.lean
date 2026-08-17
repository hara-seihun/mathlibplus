import Mathlib
import MathlibPlus.Open.ResearchFormalization.GraphClaims

namespace MathlibPlus.Open.ResearchFormalization.R0712Claim24152

open MathlibPlus.Open.ResearchFormalization.GraphClaims

noncomputable section

/-- Conjugacy of the two right-regular copies after identifying the two
    index-two Cayley presentations with the common complete-bipartite graph. -/
def correspondingRegularActionsConjugate
    {G : Type} [Fintype G] [Group G]
    (H K : Subgroup G) : Prop :=
  (∀ g : G, graphAutomorphism (indexTwoCayley (G := G) H) (Equiv.mulRight g)) ∧
    (∀ g : G, graphAutomorphism (indexTwoCayley (G := G) K) (Equiv.mulRight g)) ∧
    ∃ φ : Equiv.Perm G,
      (∀ x y : G,
        (indexTwoCayley (G := G) H).Adj x y ↔
          (indexTwoCayley (G := G) K).Adj (φ x) (φ y)) ∧
      (∀ g : G, ∃ h : G,
        φ * Equiv.mulRight g * φ⁻¹ = Equiv.mulRight h) ∧
      (∀ h : G, ∃ g : G,
        φ⁻¹ * Equiv.mulRight h * φ = Equiv.mulRight g)

/-- Claim 24152: nonisomorphic index-two subgroups rule out conjugacy of the
    corresponding regular actions in the common complete-bipartite graph. -/
def nonisomorphicIndexTwoSubgroupsGiveNonconjugateRegularActions_claim24152 : Prop :=
  ∀ {G : Type} [Fintype G] [Group G]
    (H K : Subgroup G),
    indexTwoSubgroup (G := G) H → indexTwoSubgroup (G := G) K →
    ¬ Nonempty (H ≃* K) →
    ¬ correspondingRegularActionsConjugate H K

end

end MathlibPlus.Open.ResearchFormalization.R0712Claim24152
