import MathlibPlus.Open.Analysis.Claim18793
import MathlibPlus.Analysis.Claim19058
import MathlibPlus.Open.ResearchFormalization.R0233Claim19061

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0233Claim19065

noncomputable section

/-- The physical reciprocal-scale theta mixture used by the counterexample. -/
noncomputable def reciprocalScaleThetaMixtureMeasure
    (c₀ c₁ a : ℝ) : Measure ℝ :=
  ENNReal.ofReal c₀ • MathlibPlus.Open.Analysis.Claim18793.thetaCombMeasure +
    ENNReal.ofReal c₁ •
      (MathlibPlus.Open.Analysis.Claim18793.scaledCombMeasure (Real.sqrt a) +
        ENNReal.ofReal (Real.rpow a (-1 / 2 : ℝ)) •
          MathlibPlus.Open.Analysis.Claim18793.scaledCombMeasure
            (1 / Real.sqrt a))

/-- The one-pair centered Mellin multiplier. -/
def onePairMultiplier (c₀ c₁ a : ℝ) (z : ℂ) : ℂ :=
  (c₀ : ℂ) +
    2 * ((c₁ * Real.rpow a (-1 / 4 : ℝ) : ℝ) : ℂ) *
      Complex.cosh (((Real.log a / 2 : ℝ) : ℂ) * z)

/-- The completed Mellin transform attached to the same one-pair mixture. -/
def completedOnePairMellin (c₀ c₁ a : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta s *
    onePairMultiplier c₀ c₁ a (s - (1 / 2 : ℂ))

/-- The exact centered zero lattice after reducing the multiplier to
`C + cosh (L z)`. -/
def onePairZeroLattice (C L : ℝ) : Set ℂ :=
  {z : ℂ |
    ∃ (k : ℤ) (ε : ℤ),
      (ε = -1 ∨ ε = 1) ∧
        z =
          (((ε : ℂ) * (Real.arcosh C : ℂ) +
              ((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I) /
            (L : ℂ))}

/-- Claim 19065: the reciprocal-scale theta mixture is positive, tempered,
pure-point, and Fourier-self-dual; its completed Mellin transform obeys the
centered equation, is strictly positive on the whole critical axis, and has
infinitely many off-critical zero quartets. -/
def claim19065 : Prop :=
  ∃ (C L c₀ c₁ a : ℝ) (μ : Measure ℝ),
    1 < C ∧
      0 < L ∧
        1 < a ∧
          0 < c₀ ∧
            0 < c₁ ∧
            2 * c₁ * Real.rpow a (-1 / 4 : ℝ) < c₀ ∧
              C = c₀ / (2 * c₁ * Real.rpow a (-1 / 4 : ℝ)) ∧
                L = Real.log a / 2 ∧
                  μ = reciprocalScaleThetaMixtureMeasure c₀ c₁ a ∧
                    MathlibPlus.Open.Analysis.Claim18793.positiveTemperedFourierSelfDual μ ∧
                      (∀ z : ℂ,
                        onePairMultiplier c₀ c₁ a z =
                          (2 * c₁ * Real.rpow a (-1 / 4 : ℝ) : ℂ) *
                            ((C : ℂ) + Complex.cosh ((L : ℂ) * z))) ∧
                        (∀ t : ℝ,
                          (onePairMultiplier c₀ c₁ a
                              ((t : ℂ) * Complex.I)).im = 0 ∧
                            0 <
                              (onePairMultiplier c₀ c₁ a
                                ((t : ℂ) * Complex.I)).re ∧
                            (completedOnePairMellin c₀ c₁ a
                                ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
                            0 <
                              (completedOnePairMellin c₀ c₁ a
                                ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) ∧
                          (∀ z : ℂ,
                            onePairMultiplier c₀ c₁ a z = 0 ↔
                              z ∈ onePairZeroLattice C L) ∧
                            (∀ z : ℂ,
                              z ∈ onePairZeroLattice C L →
                                completedOnePairMellin c₀ c₁ a
                                    ((1 / 2 : ℂ) + z) = 0 ∧
                                  z.re ≠ 0) ∧
                              Set.Infinite (onePairZeroLattice C L) ∧
                                (∀ z : ℂ,
                                  z ∈ onePairZeroLattice C L →
                                    star z ∈ onePairZeroLattice C L ∧
                                      -z ∈ onePairZeroLattice C L ∧
                                        -star z ∈ onePairZeroLattice C L) ∧
                                  (∀ z : ℂ,
                                    completedOnePairMellin c₀ c₁ a
                                        ((1 / 2 : ℂ) + z) =
                                      completedOnePairMellin c₀ c₁ a
                                        ((1 / 2 : ℂ) - z))

end

end MathlibPlus.Open.ResearchFormalization.R0233Claim19065
