import Mathlib

namespace MathlibPlus.NumberTheory.Claim31717

/-!
Claim 31717.  The source calls `d` an integer in the degree discussion;
ordinary degree exponents are formalized here as natural numbers.  Allowing
negative z-powers would be a different statement over a field, not an
additional degree case.
-/

/-- No natural degree exponent has `27^d = 3^7`. -/
theorem noNatural27Power : ∀ d : ℕ, 27 ^ d ≠ 3 ^ 7 := by
  intro d h
  by_cases hd : d ≤ 2
  · interval_cases d <;> norm_num at h
  · have hd3 : 3 ≤ d := by omega
    have hpow : 27 ^ 3 ≤ 27 ^ d := by
      exact Nat.pow_le_pow_right (by omega) hd3
    norm_num at hpow
    omega

end MathlibPlus.NumberTheory.Claim31717
