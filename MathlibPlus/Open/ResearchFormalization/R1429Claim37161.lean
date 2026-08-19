import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1429Claim37161

/-- Claim 37161: a linear equivalence fixing the central direct-summand
factor pointwise and descending to the quotient has the indicated triangular
form. -/
def claim37161 : Prop :=
  ∀ {𝕜 D B : Type*} [Field 𝕜] [AddCommGroup D] [AddCommGroup B]
    [Module 𝕜 D] [Module 𝕜 B]
    (α : (D × B) ≃ₗ[𝕜] (D × B)),
    (∀ z : D, α (z, 0) = (z, 0)) →
    (∃ A : B →ₗ[𝕜] B, ∀ z : D, ∀ b : B,
      (α (z, b)).2 = A b) →
      ∃ (ℓ : B →ₗ[𝕜] D) (A : B ≃ₗ[𝕜] B),
        ∀ z : D, ∀ b : B,
          α (z, b) = (z + ℓ b, A b)

end MathlibPlus.Open.ResearchFormalization.R1429Claim37161
