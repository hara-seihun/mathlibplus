import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.NumberTheory

/--
Claim 956 (`C-0062`): for `x > 1`, the non-prime-power contribution to
Chebyshev's `psi` is bounded by the square-, cube-, and fifth-root terms.
The real powers are the `Real.rpow` convention used by Mathlib's Chebyshev
functions.
-/
theorem primePowerDecompositionBound_claim956 (x : ℝ) (_hx : 1 < x) :
    0 ≤ Chebyshev.psi x - Chebyshev.theta x ∧
      Chebyshev.psi x - Chebyshev.theta x ≤
        Chebyshev.psi (x ^ (2 : ℝ)⁻¹) +
          Chebyshev.psi (x ^ (3 : ℝ)⁻¹) +
            Chebyshev.psi (x ^ (5 : ℝ)⁻¹) := by
  exact ⟨sub_nonneg.mpr (Chebyshev.theta_le_psi x),
    Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x⟩

end MathlibPlus.NumberTheory
