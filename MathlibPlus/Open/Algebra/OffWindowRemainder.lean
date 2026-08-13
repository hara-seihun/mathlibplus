import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra

/-- Formalization of admitted claim 8681.  The off-window and diagonal
quantities are retained as their finite sums of squares, which is the sign
content of the displayed packet definitions; the actual spectral terms are
parameters of those finite sums. -/
def offWindowRemainder_nonnegative_claim8681 : Prop :=
  ∀ (α ι κ : Type*) [Fintype ι] [Fintype κ]
    (ω : ℝ) (pTerm dTerm : α → ι → ℝ) (A : α),
    0 < ω →
      let P_O : ℝ := ∑ i, (pTerm A i) ^ 2
      let D_O : ℝ := ∑ i, (dTerm A i) ^ 2
      let R_O : ℝ := (1 + ω⁻¹) * P_O + D_O
      0 ≤ R_O

end MathlibPlus.Open.Algebra

namespace MathlibPlus.Algebra

theorem offWindowRemainder_nonnegative_claim8681_proved :
    MathlibPlus.Open.Algebra.offWindowRemainder_nonnegative_claim8681 := by
  intro α ι κ _ _ ω pTerm dTerm A hω
  dsimp
  have hcoef : 0 ≤ (1 + ω⁻¹ : ℝ) := by
    exact add_nonneg (by norm_num) (inv_nonneg.mpr (le_of_lt hω))
  have hP : 0 ≤ ∑ i, (pTerm A i) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (pTerm A i)
  have hD : 0 ≤ ∑ i, (dTerm A i) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (dTerm A i)
  exact add_nonneg (mul_nonneg hcoef hP) hD

end MathlibPlus.Algebra
