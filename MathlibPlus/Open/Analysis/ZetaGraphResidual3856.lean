import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.ZetaGraphResidual

open MeasureTheory Set

def intervalMellin3856 (a b : ℝ) (p : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Icc a b, Complex.exp ((s - 1) * Complex.log (x : ℂ)) * p x

def zetaGraphResidual3856 (a b : ℝ) (p q : ℝ → ℂ) (s : ℂ) : ℂ :=
  intervalMellin3856 a b p s - riemannZeta s * intervalMellin3856 a b q s

def sourceL1Norm3856 (a b : ℝ) (p : ℝ → ℂ) : ℝ :=
  ∫ x in Icc a b, ‖p x‖

def denominatorFreeZetaCrossResidual3856 : Prop :=
  ∀ (a b : ℝ) (p q : ℝ → ℂ),
    0 < a →
    a ≤ b →
    MeasureTheory.IntegrableOn p (Icc a b) →
    MeasureTheory.IntegrableOn q (Icc a b) →
    sourceL1Norm3856 a b p + sourceL1Norm3856 a b q = 1 →
    ContinuousOn (fun s : ℂ => zetaGraphResidual3856 a b p q s)
      {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → intervalMellin3856 a b q s = 0 →
      zetaGraphResidual3856 a b p q s = intervalMellin3856 a b p s)

end MathlibPlus.Open.Analysis.ZetaGraphResidual
