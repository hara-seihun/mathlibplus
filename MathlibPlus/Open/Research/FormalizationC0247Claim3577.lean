import MathlibPlus.Open.Research.FormalizationReset

namespace MathlibPlus.Open.Research.FormalizationC0247Claim3577

noncomputable section

/-- The compact full-gap B-spline window on an interval, using the reviewed
centered reset-window carrier. -/
def claim3577 : Prop :=
  ∀ (I : Set ℝ) (u v S L : ℝ) (m : ℕ),
    I = Set.Icc u v →
    S = v - u →
    0 < S →
    8 ≤ L * S →
    m = Int.toNat (Int.floor (L * S / 4)) →
    ∀ x : ℝ,
      resetOmegaDensity u v L x =
        resetConvolution (resetV S)
          (resetConvolutionPower (resetB S m) m)
          (x - (u + v) / 2)

end

end MathlibPlus.Open.Research.FormalizationC0247Claim3577
