import Mathlib

namespace MathlibPlus.NumberTheory.Claim17974

/--
Claim 17974.  Complementary-divisor exchange squares to the identity.  The
source's divisor domain is not typed; this exact field-level statement uses a
nonzero parameter and Lean's total division, so it also covers input `m = 0`.
-/
theorem complementaryDivisorExchange_involutive
    {K : Type*} [Field K] {α : Type*}
    (k : K) (hk : k ≠ 0) (f : K → α) :
    (fun m => f (k / (k / m))) = f := by
  funext m
  by_cases hm : m = 0
  · simp [hm]
  · congr 1
    field_simp

end MathlibPlus.NumberTheory.Claim17974
