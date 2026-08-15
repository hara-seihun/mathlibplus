import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Simultaneous arbitrary-tail extension. -/

def claim59732 : Prop :=
  ∀ (a : ℕ → ℚ) (b : ℕ → ℕ),
    ∃ (m : ℕ → ℚ) (μ : ℕ → ℕ),
      m 2 = (1 / 2 : ℚ) ∧
      m 3 = 2 ∧
      m 4 = 24 ∧
      m 5 = 1152 ∧
      m 6 = 276480 ∧
      m 7 = 398131200 ∧
      (∀ r : ℕ, 3 ≤ r → r ≤ 7 →
        m r = 2 * (Nat.factorial (r - 1) : ℚ) * m (r - 1)) ∧
      (∀ r : ℕ, 2 ≤ r → r ≤ 7 → μ r = Nat.factorial (r - 2)) ∧
      (∀ r : ℕ, 8 ≤ r → m r = a r) ∧
      (∀ r : ℕ, 8 ≤ r → μ r = b r)


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
