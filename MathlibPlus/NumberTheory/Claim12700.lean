import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim12700

/-!
The first exact arithmetic mismatch from claim 12700.  The source's wider
VOA/conformal-net obstruction is not encoded here because those source
structures are not supplied as canonical Lean objects; this theorem retains
the exact local Euler coefficient calculation and its all-repeat inequality.
-/

/-- The first repeat coefficient is `σ₁(2)/2 = 3/2`, rather than the
Euler coefficient `1/2`; at every repeat index `k > 1`, the descendant
coefficient `σ₁(k)/k` differs from the required `1/k`. -/
theorem firstEulerMismatch :
    (((ArithmeticFunction.sigma 1 2 : ℕ) : ℚ) / 2 = 3 / 2) ∧
      (((ArithmeticFunction.sigma 1 2 : ℕ) : ℚ) / 2 ≠ 1 / 2) ∧
      ∀ k : ℕ, 1 < k →
        1 < ArithmeticFunction.sigma 1 k ∧
          ((ArithmeticFunction.sigma 1 k : ℕ) : ℚ) / k ≠ (1 : ℚ) / k := by
  constructor
  · norm_num [ArithmeticFunction.sigma_apply]
  constructor
  · norm_num [ArithmeticFunction.sigma_apply]
  · intro k hk
    have hk0 : k ≠ 0 := by omega
    have hpos : 0 < ArithmeticFunction.sigma 1 k :=
      ArithmeticFunction.sigma_pos 1 k hk0
    have hne : ArithmeticFunction.sigma 1 k ≠ 1 := by
      intro h
      have hone : k = 1 :=
        (ArithmeticFunction.sigma_eq_one_iff 1 k).mp h
      omega
    constructor
    · omega
    · have hkq : (k : ℚ) ≠ 0 := by
        exact_mod_cast hk0
      intro hcoeff
      have hcoeff' : (ArithmeticFunction.sigma 1 k : ℚ) = 1 := by
        field_simp [hkq] at hcoeff
        exact hcoeff
      exact hne (by exact_mod_cast hcoeff')

end MathlibPlus.NumberTheory.Claim12700
