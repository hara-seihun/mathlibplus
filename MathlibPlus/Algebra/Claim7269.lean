import Mathlib

namespace MathlibPlus.Algebra.Claim7269

/-- A polynomial family whose positive-degree coefficients are boundary-independent
and whose constant coefficient is affine in the boundary parameter. -/
def IsConstantBoundaryFamily {R : Type*} [CommRing R]
    (P : R → Polynomial R) : Prop :=
  (∃ a d : R, ∀ b : R, (P b).coeff 0 = a * b + d) ∧
    ∀ n : ℕ, 0 < n → ∀ b₁ b₂ : R,
      (P b₁).coeff n = (P b₂).coeff n

end MathlibPlus.Algebra.Claim7269
