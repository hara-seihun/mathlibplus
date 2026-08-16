import Mathlib

namespace MathlibPlus.Open.Combinatorics.NevilleGamma

noncomputable section

/-- The exact lower-triangular gamma--Darboux Neville multiplier. -/
def gammaDarbouxNevilleMultiplier (α : ℝ) (r c : ℕ) : ℝ :=
  (((2 : ℝ) * r - 1) * (α + r)) /
    ((2 : ℝ) * r * ((2 : ℝ) * r + 2 * c - 1) *
      ((2 : ℝ) * r + 2 * c + 1))

/-- The exact first vertical ratio of the gamma--Darboux Neville triangle. -/
def exactFirstVerticalRatio_claim14814 : Prop :=
  ∀ (α : ℝ) (c : ℕ), -1 < α →
    gammaDarbouxNevilleMultiplier α (c + 2) c /
        gammaDarbouxNevilleMultiplier α (c + 1) c =
      (((c + 1 : ℕ) : ℝ) * ((2 * c + 3 : ℕ) : ℝ) *
          ((4 * c + 1 : ℕ) : ℝ) * (α + c + 2)) /
        (((c + 2 : ℕ) : ℝ) * ((2 * c + 1 : ℕ) : ℝ) *
          ((4 * c + 5 : ℕ) : ℝ) * (α + c + 1))

end
end MathlibPlus.Open.Combinatorics.NevilleGamma
