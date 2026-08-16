import Mathlib

open scoped BigOperators Interval Topology
open Filter

namespace MathlibPlus.Open.ResearchFormalization.O0310SelectedZeroGain

noncomputable section

/-- The lower-tail rate used for the exponential cutoff regime. -/
def lowerTailRate (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then u - 1 - Real.log u else 0

/-- The cutoff determined by the fixed ratio `r` in `log X = r k / d`. -/
def selectedCutoff (k : ℕ) (d r : ℝ) : ℝ :=
  Real.exp (r * (k : ℝ) / d)

/-- The exact selected-zero contribution from the truncated packet. -/
def selectedZeroTerm (k : ℕ) (d X : ℝ) : ℝ :=
  -((Nat.factorial (k - 1) : ℝ)⁻¹) *
    ∫ y in (0 : ℝ)..Real.log X,
      y ^ (k - 1) * Real.exp (-d * y)

/-- The square root of the literal truncated diagonal model. -/
def literalDiagonalRoot (k : ℕ) (c X : ℝ) : ℝ :=
  ((Nat.factorial (k - 1) : ℝ)⁻¹) *
    Real.sqrt
      (∫ y in (0 : ℝ)..Real.log X,
        y ^ (2 * k - 1) * Real.exp (-2 * c * y))

/-- The selected-zero squared gain over the literal truncated diagonal. -/
def selectedGain (k : ℕ) (c d r : ℝ) : ℝ :=
  (|selectedZeroTerm k d (selectedCutoff k d r)| /
      literalDiagonalRoot k c (selectedCutoff k d r)) ^ 2

/-- The exponent asserted for the selected-zero squared gain. -/
def gainExponent (c d r : ℝ) : ℝ :=
  2 * Real.log (c / d) - 2 * lowerTailRate r +
    2 * lowerTailRate (c * r / d)

/-- Claim 15264: the selected-zero squared gain has exponent `E(r)`. -/
def claim15264 : Prop :=
  ∀ c d r : ℝ, 0 < c → 0 < d → 0 < r →
    Filter.Tendsto
      (fun k : ℕ =>
        (Real.log (selectedGain k c d r) -
            (k : ℝ) * gainExponent c d r) / (k : ℝ))
      Filter.atTop (𝓝 0)

/-- Claim 15265: before the diagonal saddle both lower-tail rates are active,
with gain `X^(2*δ+o(1))`, hence the gain is `o(X)`. -/
def claim15265 : Prop :=
  ∀ c d δ r : ℝ,
    0 < c → 0 < d → 0 < δ → d = c - δ → 0 < r →
      r ≤ d / c → 2 * δ < 1 →
    lowerTailRate r - lowerTailRate (c * r / d) =
        Real.log (c / d) - r * δ / d ∧
      gainExponent c d r = 2 * r * δ / d ∧
      Filter.Tendsto
        (fun k : ℕ =>
          Real.log (selectedGain k c d r) /
            Real.log (selectedCutoff k d r))
        Filter.atTop (𝓝 (2 * δ)) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          selectedGain k c d r / selectedCutoff k d r)
        Filter.atTop (𝓝 0)

end

end MathlibPlus.Open.ResearchFormalization.O0310SelectedZeroGain
