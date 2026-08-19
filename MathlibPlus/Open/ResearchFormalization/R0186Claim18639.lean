import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0186Claim18639

/-- Claim 18639: every displayed certified coefficient is strictly positive
at each natural index n >= 3. -/
def strictCertifiedCoefficientPositivity_claim18639 : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    0 <
      ((2 : ℝ) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
        (64 * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) +
          6 * (4 : ℝ) ^ n)

end MathlibPlus.Open.ResearchFormalization.R0186Claim18639
