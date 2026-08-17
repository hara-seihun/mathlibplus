import MathlibPlus.Analysis.Claim13408
import MathlibPlus.Open.Analysis.Claim13423

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0085

noncomputable section

/-- Claim 13409: the finite sharp-prefix kernel has Mellin transform
`Gamma(s) * A_y(2-s)` throughout the half-plane `Re(s) > 0`. -/
def claim13409 : Prop :=
  ∀ (y : ℕ) (s : ℂ), 0 < s.re →
    (MeasureTheory.integral
      (volume.restrict (Set.Ioi (0 : ℝ)))
      (fun x =>
        (MathlibPlus.Open.Analysis.Claim13423.sharpKernel y x : ℂ) *
          Complex.cpow (x : ℂ) (s - 1))) =
      Complex.Gamma s *
        MathlibPlus.Analysis.Claim13408.finiteEulerProduct y (2 - s)

end
end MathlibPlus.Open.Analysis.FormalizationBatchO0085
