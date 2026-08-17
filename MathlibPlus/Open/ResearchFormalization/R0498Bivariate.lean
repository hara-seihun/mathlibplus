import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0498Bivariate

noncomputable section

abbrev BivariateSeries := MvPowerSeries (Fin 2) ℚ

/-- The explicit positive-part formula for the ceiling `U`; the bivariate
coefficient carrier below keeps only the source range `ell ≥ 1`. -/
def ceilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

def xVariable : BivariateSeries := MvPowerSeries.X 0

def zVariable : BivariateSeries := MvPowerSeries.X 1

/-- The coefficient at `x^ell z^N` of the source bivariate ceiling series. -/
def bivariateCeilingSeries : BivariateSeries :=
  fun d => if 1 ≤ d 0 then (ceilingU (d 0) (d 1) : ℚ) else 0

def bivariateCeilingRationalRhs : BivariateSeries :=
  xVariable * ((1 - xVariable) * (1 - zVariable))⁻¹ +
    xVariable ^ 3 * zVariable ^ 2 *
      ((1 - xVariable) * (1 - xVariable ^ 2 * zVariable ^ 2) *
        (1 - zVariable) ^ 2)⁻¹ +
    xVariable ^ 2 * zVariable ^ 2 *
      ((1 - xVariable ^ 2 * zVariable ^ 2) * (1 - zVariable) ^ 2 *
        (1 + zVariable))⁻¹

/-- Claim 29360: the bivariate ceiling series equals the displayed rational
formal power series. -/
def bivariateCeilingSeriesIdentity : Prop :=
  bivariateCeilingSeries = bivariateCeilingRationalRhs

end
end MathlibPlus.Open.ResearchFormalization.R0498Bivariate
