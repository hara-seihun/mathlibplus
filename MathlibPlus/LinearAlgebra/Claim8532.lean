import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra.Claim8532

/--
For an exact free squared-Jacobi block, the paired lifted coefficients at an
interior edge have the normalized square-root formulas and multiply to the
free off-diagonal value.  The positive hypotheses are the pointwise
consequence of the positive Jacobi factorization in the source packet.
-/
theorem pairedLiftCoefficients (a k b : ℕ) (_hak : a ≤ k) (_hkb : k < b)
    {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    let δ : ℝ := q / c - 1
    let r : ℝ := Real.sqrt q
    let sNext : ℝ := c / Real.sqrt q
    r / Real.sqrt c = Real.sqrt (1 + δ) ∧
      sNext / Real.sqrt c = 1 / Real.sqrt (1 + δ) ∧
      r * sNext = c := by
  dsimp
  have hc0 : 0 ≤ c := hc.le
  have hq0 : 0 ≤ q := hq.le
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hratio : 1 + (q / c - 1) = q / c := by ring
  have hsqrt_div : Real.sqrt (q / c) = Real.sqrt q / Real.sqrt c :=
    Real.sqrt_div hq0 c
  rw [hratio]
  constructor
  · exact hsqrt_div.symm
  constructor
  · rw [hsqrt_div]
    field_simp [hsqrtq.ne', hsqrtc.ne']
    exact (Real.sq_sqrt hc0).symm
  · have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
    field_simp [hsqrtq.ne', hsq]

end MathlibPlus.LinearAlgebra.Claim8532
