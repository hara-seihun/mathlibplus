import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact MRS kernel integrals

Registry statement for admitted claim 466.  The integrals are oriented interval
Lebesgue integrals over `[0, 1]`; the endpoint value at the square-root
singularity is immaterial.
-/

namespace MathlibPlus.Open.Analysis

/-- The two exact kernel integrals used in the MRS asymptotic calculation. -/
def exactMRSKernelIntegrals : Prop :=
  (∫ t : ℝ in 0..1, t / Real.sqrt (1 - t ^ 2)) = 1 ∧
    (∫ t : ℝ in 0..1, t * Real.log t / Real.sqrt (1 - t ^ 2)) =
      Real.log 2 - 1

end MathlibPlus.Open.Analysis
