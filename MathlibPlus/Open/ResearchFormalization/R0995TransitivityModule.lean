import MathlibPlus.Open.Research.TransitivityModule

namespace MathlibPlus.Open.ResearchFormalization.R0995TransitivityModule

noncomputable section

open MathlibPlus.Open.Research.TransitivityModule

private def groupAlgebraInvolution {H : Type*} [Group H]
    (a : MonoidAlgebra ℚ H) : MonoidAlgebra ℚ H :=
  MonoidAlgebra.ofCoeff
    (Finsupp.mapDomain (fun h : H => h⁻¹) a.coeff)

private def sRingOverOrbitModule {H : Type*} [Fintype H] [Group H]
    (orbits : Set (Set H))
    (M : Submodule ℚ (MonoidAlgebra ℚ H)) : Prop :=
  (1 : MonoidAlgebra ℚ H) ∈ M ∧
    (∀ a b : MonoidAlgebra ℚ H,
      a ∈ M → b ∈ M → a * b ∈ M) ∧
    (∀ a : MonoidAlgebra ℚ H, a ∈ M →
      groupAlgebraInvolution a ∈ M) ∧
    (∀ T, T ∈ orbits → simpleQuantity H T ∈ M) ∧
    (∀ a : MonoidAlgebra ℚ H, a ∈ M →
      ∀ T, T ∈ orbits → ∀ x ∈ T, ∀ y ∈ T,
        a.coeff x = a.coeff y)

/-- Claim 28083: the concrete point-stabilizer orbit span in the group
algebra is an S-ring over H, with its orbit-sum basis, multiplication and
inversion closure, and coefficient constancy on the exact orbit partition. -/
def wielandtTransitivityModuleIsSRing_claim28083 : Prop :=
  ∀ (H : Type*) [Fintype H] [Group H]
    (G : Subgroup (Equiv.Perm H)),
    rightRegularSubgroup H ≤ G →
      sRingOverOrbitModule
        (pointStabilizerOrbits H G)
        (transitivityModule H G)

end

end MathlibPlus.Open.ResearchFormalization.R0995TransitivityModule
