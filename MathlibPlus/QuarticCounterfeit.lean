import Mathlib

/-!
# Quartic off-axis counterfeit

Exact polynomial facts extracted from source record `C-0035`.  The analytic Rouché
transfer to a perturbed completed-zeta source is not asserted here.
-/

namespace MathlibPlus.QuarticCounterfeit

/-- The packet's quartic is strictly positive on the real axis. -/
theorem quartic_positiveOnReal (x : ℝ) :
    0 < x ^ 4 + 6 * x ^ 2 + 25 := by
  nlinarith [sq_nonneg (x ^ 2 + 3)]

/-- The four displayed roots of `z⁴ + 6z² + 25` are all nonreal. -/
theorem quartic_hasOffAxisZeros :
    ∀ z ∈ ({(1 + 2 * Complex.I), (1 - 2 * Complex.I),
        (-1 + 2 * Complex.I), (-1 - 2 * Complex.I)} : Set ℂ),
      z ^ 4 + 6 * z ^ 2 + 25 = 0 ∧ z.im ≠ 0 := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> constructor <;>
    norm_num [Complex.ext_iff, pow_succ]

end MathlibPlus.QuarticCounterfeit
