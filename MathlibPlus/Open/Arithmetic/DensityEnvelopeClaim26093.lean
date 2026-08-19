import Mathlib

namespace MathlibPlus.Open.Arithmetic

/-- Claim 26093: for D at least three, the displayed integer density
function is nondecreasing on its full interval.  Natural-number division is
the floor in the displayed nonnegative formula. -/
def densityEnvelopeMonotone_claim26093 : Prop :=
  ∀ D : ℕ, 3 ≤ D →
    let hD : ℕ := (D - 1) / 2
    ∀ q₁ q₂ : ℕ, q₁ ≤ q₂ → q₂ ≤ D →
      (D - q₁) ^ 2 / 9 + q₁ * hD ≤
        (D - q₂) ^ 2 / 9 + q₂ * hD

end MathlibPlus.Open.Arithmetic
