import Mathlib

namespace MathlibPlus.Open.Analysis

/--
Exceptional zeroth-kernel Laplace transform.  The zeroth kernel is represented
by the admitted Poisson--Charlier series from Claim 10208.
-/
def exceptionalZerothKernelLaplaceTransform : Prop :=
  ∀ x s : ℝ,
    0 < x →
    0 < s →
    (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-s * t) *
          (∑' k : ℕ,
            ((-1 : ℝ) ^ k * x ^ (k + 1) * t ^ k) /
              ((Nat.factorial k : ℝ) * (Nat.factorial (k + 1) : ℝ)))) =
      1 - Real.exp (-x / s)

end MathlibPlus.Open.Analysis
