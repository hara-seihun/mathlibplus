import Mathlib

namespace MathlibPlus.Open.Analysis.GainBetweenSaddles15266

noncomputable section

/-- The lower-tail rate used by the selected-zero gain exponent. -/
private def lowerTailRate15266 (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then u - 1 - Real.log u else 0

/-- The exact gain exponent from the selected-zero comparison. -/
private def selectedZeroGainExponent15266 (c d r : ℝ) : ℝ :=
  2 * Real.log (c / d) -
    2 * lowerTailRate15266 r +
    2 * lowerTailRate15266 (c * r / d)

/-- The smooth expression for `H=E-r/d` on the regime between the two saddles.
It is the middle-regime expression of the displayed gain exponent, extended
only so that its stationary point can be named and differentiated. -/
private def middleGainH15266 (c d r : ℝ) : ℝ :=
  2 * Real.log (c / d) - 2 * r + 2 + 2 * Real.log r - r / d

/-- The stationary point named in the gain comparison. -/
private def stationaryPoint15266 (d : ℝ) : ℝ :=
  2 * d / (2 * d + 1)

/-- Gain between the diagonal and zero saddles, with the exact rate carrier,
stationary-point condition, regime equivalence, boundary value, monotonicity,
and strict negative conclusion retained. -/
def gainBetweenDiagonalAndZeroSaddles15266 : Prop :=
  ∀ (c d δ : ℝ),
    0 < d →
    0 < δ →
    c = d + δ →
      ((2 * δ < 1 ↔ stationaryPoint15266 d < d / c) ∧
        deriv (middleGainH15266 c d) (stationaryPoint15266 d) = 0 ∧
        middleGainH15266 c d (d / c) = -(1 - 2 * δ) / c ∧
        (∀ r : ℝ,
          d / c ≤ r → r ≤ 1 →
            middleGainH15266 c d r =
              selectedZeroGainExponent15266 c d r - r / d) ∧
        (2 * δ < 1 →
          (∀ x y : ℝ,
            d / c ≤ x → x ≤ y → y ≤ 1 →
              middleGainH15266 c d y ≤ middleGainH15266 c d x) ∧
          (∀ r : ℝ,
            d / c ≤ r → r ≤ 1 →
              middleGainH15266 c d r ≤
                  middleGainH15266 c d (d / c) ∧
                middleGainH15266 c d (d / c) =
                  -(1 - 2 * δ) / c ∧
                -(1 - 2 * δ) / c < 0)))

end

end MathlibPlus.Open.Analysis.GainBetweenSaddles15266
