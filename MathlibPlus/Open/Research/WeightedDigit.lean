import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

/-- The weighted fractional-part series from the admitted base-expansion claim. -/
def rho (b : ℕ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, Int.fract ((b : ℝ) ^ j * x) / (b : ℝ) ^ j

/-- A canonical base-`b` expansion of a real number in the unit interval.
The final condition excludes the noncanonical expansion that is eventually all
`b - 1`. -/
def HasCanonicalBaseExpansion (b : ℕ) (x : ℝ) (d : ℕ → ℕ) : Prop :=
  (∀ j, d j < b) ∧
    x = ∑' j : ℕ, (d j : ℝ) / (b : ℝ) ^ (j + 1) ∧
    ¬ (∃ N, ∀ j, N ≤ j → d j + 1 = b)

/-- The admitted weighted-digit identity, with `d j` denoting the digit in
position `j + 1`. -/
def weightedDigitIdentity : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (d : ℕ → ℕ),
    HasCanonicalBaseExpansion b x d →
      rho b x = ∑' j : ℕ, (j + 1 : ℝ) * d j / (b : ℝ) ^ (j + 1)

end

end MathlibPlus.Open.Research
