import Mathlib

open Set MeasureTheory

namespace MathlibPlus.Open.Analysis.RegularizedBoseMellinClaim14060

noncomputable section

private def boseQ (x : ℝ) : ℝ :=
  1 / x - 1 / (Real.exp x - 1)

private def boseMellin (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ),
    Complex.cpow (x : ℂ) (s - (1 : ℂ)) * (boseQ x : ℂ)

def claim14060 : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    boseMellin s = -Complex.Gamma s * riemannZeta s

end

end MathlibPlus.Open.Analysis.RegularizedBoseMellinClaim14060
