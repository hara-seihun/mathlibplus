import MathlibPlus.Basic

open BigOperators

namespace MathlibPlus.NumberTheory

/-- The two finite prime-divisor Euler products in claim 10734 have distinct
exact rational values. -/
theorem finiteEulerProductsSeparate_claim10734 :
    (∏ p ∈ Nat.primeFactors 35, (1 - (p : ℚ)⁻¹)⁻¹) = 35 / 24 ∧
      (∏ p ∈ Nat.primeFactors 39, (1 - (p : ℚ)⁻¹)⁻¹) = 13 / 8 ∧
      (35 / 24 : ℚ) ≠ 13 / 8 := by
  have h35 : Nat.primeFactors 35 = ({5, 7} : Finset ℕ) := by
    native_decide
  have h39 : Nat.primeFactors 39 = ({3, 13} : Finset ℕ) := by
    native_decide
  rw [h35, h39]
  norm_num

end MathlibPlus.NumberTheory
