import MathlibPlus.Basic

namespace MathlibPlus.Analysis.RiemannBranchCrossover

/-!
Formalization of admitted claim 1230.  The source does not specify a domain
for `T`; this statement therefore quantifies over real `T` exactly as written
and uses its displayed threshold on `Real.log T`.
-/

/-- Above the displayed logarithmic threshold, branch A's affine error term is
no larger than branch B's. -/
theorem branchCrossoverAtLogThreshold (T : ℝ)
    (hT : (326.488 : ℝ) ≤ Real.log T) :
    (0.094561625 : ℝ) * Real.log T + 5.571609 ≤
      0.09699991989825 * Real.log T + 4.775537 := by
  nlinarith

end MathlibPlus.Analysis.RiemannBranchCrossover
