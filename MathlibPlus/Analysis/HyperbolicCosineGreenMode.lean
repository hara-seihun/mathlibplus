import Mathlib

/-!
# Hyperbolic-cosine homogeneous Green mode

The second-derivative identity from admitted claim 17398 is stated with
`iteratedDeriv 2`, which is the Lean expression for the displayed `D²`.
-/

namespace MathlibPlus.Analysis

/-- `cosh (u / 2)` solves `(D² - 1/4) f = 0` at every real `u`. -/
theorem hyperbolicCosine_homogeneousGreenMode (u : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.cosh (x / 2)) u -
        (1 / 4 : ℝ) * Real.cosh (u / 2) = 0 := by
  have h := iteratedDeriv_comp_const_mul (f := Real.cosh) (n := 2)
    Real.contDiff_cosh (1 / 2 : ℝ)
  have hu := congrFun h u
  calc
    iteratedDeriv 2 (fun x : ℝ => Real.cosh (x / 2)) u -
        (1 / 4 : ℝ) * Real.cosh (u / 2) =
        (1 / 2 : ℝ) ^ 2 * Real.cosh (u / 2) -
          (1 / 4 : ℝ) * Real.cosh (u / 2) := by
      rw [show (2 : ℕ) = 2 * 1 by norm_num] at hu
      rw [Real.iteratedDeriv_even_cosh] at hu
      convert congrArg (fun z : ℝ => z -
        (1 / 4 : ℝ) * Real.cosh (u / 2)) hu using 1 <;> ring
    _ = 0 := by ring

end MathlibPlus.Analysis
