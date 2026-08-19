import Mathlib

namespace MathlibPlus.Combinatorics.R0414

/-- Claim 21130: the exact balance consequences used by the quadratic
pair-product contradiction force the base count above six.  The singleton
product theorem and the small-u pair consequence are retained as explicit
source hypotheses, while all displayed balance coordinates remain in the
statement. -/
def quadraticPairProductForcesSevenBaseMembers_claim21130 : Prop :=
  ∀ (N d : ℕ) (u₁₂ u₁₃ u₂₃ e a₁ a₂ a₃ : ℕ),
    13 ≤ N →
    d = u₁₂ + u₁₃ + u₂₃ + 2 * e →
    a₁ = N + 2 - u₁₂ - u₁₃ - e →
    a₂ = N + 2 - u₁₂ - u₂₃ - e →
    a₃ = N + 2 - u₁₃ - u₂₃ - e →
    (d ≤ 6 → u₁₂ ≤ 2 ∨ u₁₃ ≤ 2 ∨ u₂₃ ≤ 2) →
    (u₁₂ ≤ 2 → a₁ * a₂ ≤ 80) →
    (u₁₃ ≤ 2 → a₁ * a₃ ≤ 80) →
    (u₂₃ ≤ 2 → a₂ * a₃ ≤ 80) →
    (u₁₂ ≤ 2 → 9 ≤ a₁ ∧ 9 ≤ a₂ ∧ 24 ≤ a₁ + a₂) →
    (u₁₃ ≤ 2 → 9 ≤ a₁ ∧ 9 ≤ a₃ ∧ 24 ≤ a₁ + a₃) →
    (u₂₃ ≤ 2 → 9 ≤ a₂ ∧ 9 ≤ a₃ ∧ 24 ≤ a₂ + a₃) →
    7 ≤ d

end MathlibPlus.Combinatorics.R0414
