import MathlibPlus.AxlerMajorant

namespace MathlibPlus.Analysis.Claim628

noncomputable section

/-- Claim 628's eight-term family, with the displayed decimal coefficients
represented by Lean's exact rational decimal literals. -/
def primeCountingFamily (c x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    6.024334 * x / L ^ 4 +
    24.024334 * x / L ^ 5 +
    120.12167 * x / L ^ 6 +
    720.73002 * x / L ^ 7 +
    c * x / L ^ 8

/-- The generic family deliberately refactors the already canonical fixed
majorant: at the source's eighth coefficient `6097.2 = 30486/5`, it is
kernel-checked equal to `AxlerMajorant.predecessorBound`. -/
theorem primeCountingFamily_at_predecessor (x : ℝ) :
    primeCountingFamily (6097.2 : ℝ) x =
      MathlibPlus.AxlerMajorant.predecessorBound x := by
  norm_num [primeCountingFamily, MathlibPlus.AxlerMajorant.predecessorBound]

end

end MathlibPlus.Analysis.Claim628
