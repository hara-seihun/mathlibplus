import MathlibPlus.Open.NumberTheory.Claim9192

namespace MathlibPlus.Open.NumberTheory.ExteriorProductClaim9188

open Classical
open MathlibPlus.Open.NumberTheory.Claim9192
open scoped BigOperators

noncomputable def orbitBlock9188 (α : ℂ)
    (σ : ℂ ≃ₐ[ℚ] ℂ) : Finset ℂ :=
  (exteriorRoots α).image σ

noncomputable def orbitBlockProduct9188 (α : ℂ)
    (σ : ℂ ≃ₐ[ℚ] ℂ) : ℂ :=
  Finset.prod (orbitBlock9188 α σ) (fun z => z)

/-- The full automorphism-indexed orbit-block product family, with the fixed
sign retained for every translate and with all non-distinguished conjugates
in the closed unit disk. -/
def conjugatesOfExteriorProduct_claim9188 : Prop :=
  ∀ α : ℂ,
    admissible α →
      ∃ (ε : ℂ) (β : ℝ),
        (ε = 1 ∨ ε = -1) ∧
          β = mahlerMeasure α ∧
          (β : ℂ) = ε * exteriorProduct α ∧
          0 < β ∧
          (β : ℂ) ∈ conjugateRoots (β : ℂ) ∧
          (∀ σ : ℂ ≃ₐ[ℚ] ℂ,
            orbitBlock9188 α σ ∈ exteriorOrbit α ∧
              σ (β : ℂ) =
                ε * orbitBlockProduct9188 α σ) ∧
          (∀ z : ℂ,
            z ∈ conjugateRoots (β : ℂ) ↔
              ∃ σ : ℂ ≃ₐ[ℚ] ℂ,
                z = ε * orbitBlockProduct9188 α σ) ∧
          (∀ z ∈ conjugateRoots (β : ℂ),
            z ≠ (β : ℂ) → ‖z‖ ≤ 1)

end MathlibPlus.Open.NumberTheory.ExteriorProductClaim9188
