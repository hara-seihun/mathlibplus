import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0034Claim10461

noncomputable section

/-- The finite binary occupancy factor in the displayed local coordinate. -/
def finiteBinaryOccupancyFactor_10461 : PowerSeries ℚ :=
  1 + PowerSeries.X

/-- The unbounded Euler bosonic factor in the displayed local coordinate. -/
def eulerBosonicOccupancyFactor_10461 : PowerSeries ℚ :=
  (1 - PowerSeries.X)⁻¹

/-- Coefficients of the displayed formal logarithm of the finite factor. -/
def finiteBinaryLogRepeatCoefficient_10461 (n : ℕ) : ℚ :=
  if 0 < n then (-1 : ℚ) ^ (n + 1) / (n : ℚ) else 0

/-- Coefficients of the displayed negative formal logarithm of the bosonic
factor. -/
def eulerBosonicLogRepeatCoefficient_10461 (n : ℕ) : ℚ :=
  if 0 < n then (1 : ℚ) / (n : ℚ) else 0

/-- The formal logarithmic series attached to the finite factor. -/
def finiteBinaryLogSeries_10461 : PowerSeries ℚ :=
  PowerSeries.log ℚ

/-- The formal logarithmic series attached to the inverse bosonic factor. -/
def eulerBosonicLogSeries_10461 : PowerSeries ℚ :=
  PowerSeries.logOf eulerBosonicOccupancyFactor_10461

/-- Claim 10461: the finite-coordinate logarithm has alternating repeat
coefficients, the bosonic Euler logarithm has positive repeat coefficients,
and every positive even repeat has the wrong sign. -/
def independentFiniteCoordinatesWrongRepeatSigns_claim10461_batch : Prop :=
  let finiteFactor := finiteBinaryOccupancyFactor_10461
  let bosonicFactor := eulerBosonicOccupancyFactor_10461
  finiteFactor = 1 + PowerSeries.X ∧
    bosonicFactor = (1 - PowerSeries.X)⁻¹ ∧
    (∀ n : ℕ,
      PowerSeries.coeff n finiteBinaryLogSeries_10461 =
        finiteBinaryLogRepeatCoefficient_10461 n) ∧
    (∀ n : ℕ,
      PowerSeries.coeff n eulerBosonicLogSeries_10461 =
        eulerBosonicLogRepeatCoefficient_10461 n) ∧
    (∀ n : ℕ, 0 < n → Even n →
      PowerSeries.coeff n finiteBinaryLogSeries_10461 ≠
        PowerSeries.coeff n eulerBosonicLogSeries_10461)

end
end MathlibPlus.Open.ResearchFormalization.O0034Claim10461
