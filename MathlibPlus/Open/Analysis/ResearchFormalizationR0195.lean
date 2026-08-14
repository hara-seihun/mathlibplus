import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0195

/-- The exact polynomial displayed in Claim 18712. -/
def primitiveRankFourPolynomial (c : ℝ) : ℝ :=
  11980800 * c ^ 6 - 61503232 * c ^ 5 +
    121305408 * c ^ 4 - 118057104 * c ^ 3 +
    59990700 * c ^ 2 - 15135120 * c + 1486485

/-- Claim 18712.  The packet's coefficient function remains an explicit
carrier; the polynomial is not introduced by defining it to be `F`. -/
def claim18712_primitiveRankFourConstantCoefficient (F : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, F c = primitiveRankFourPolynomial c

end MathlibPlus.Open.Analysis.ResearchFormalizationR0195
