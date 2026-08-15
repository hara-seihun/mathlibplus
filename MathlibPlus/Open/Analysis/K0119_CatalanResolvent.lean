import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 8802: the constant half-line Catalan resolvent identity. -/
def catalanResolventIdentity8802 : Prop :=
  ∀ (lam A : ℝ),
    lam > 2 * A →
    0 ≤ A →
    lam⁻¹ * ∑' r : ℕ,
        (((r + 1 : ℕ) : ℝ)⁻¹ * (Nat.choose (2 * r) r : ℝ)) *
          (A / lam) ^ (2 * r) =
      2 / (lam + Real.sqrt (lam ^ 2 - 4 * A ^ 2))

end MathlibPlus.Open.Analysis
