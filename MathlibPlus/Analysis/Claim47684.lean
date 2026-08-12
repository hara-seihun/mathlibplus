import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/--
Claim 47684 (R-3678): the displayed nested two-atom counterfeit has the stated
support ordering, increasing low/high weight ratios, and negative exact
second-moment determinant.  The theorem records the closed rational witness;
it does not identify this witness with the target exponential reciprocal law.
-/
theorem claim47684_nestedSupportCounterfeit :
    (0 : ℚ) < 1 / 4 ∧
      (1 / 4 : ℚ) < 1 / 2 ∧
      (1 / 2 : ℚ) < 3 / 4 ∧
      (3 / 4 : ℚ) < 4 / 5 ∧
      (2 : ℚ) / 1 < 100 / 1 ∧
      let moment : ℚ → ℚ → ℚ → ℚ → ℕ → ℚ :=
        fun xₗ xₕ wₗ wₕ k => wₗ * xₗ ^ k + wₕ * xₕ ^ k
      let M : Matrix (Fin 2) (Fin 2) ℚ :=
        !![moment (1 / 2) (3 / 4) 2 1 1, moment (1 / 4) (4 / 5) 100 1 1;
           moment (1 / 2) (3 / 4) 2 1 2, moment (1 / 4) (4 / 5) 100 1 2]
      M.det = -3071 / 200 ∧
        (-3071 / 200 : ℚ) < 0 := by
  norm_num [Matrix.det_fin_two]

end MathlibPlus.Analysis
