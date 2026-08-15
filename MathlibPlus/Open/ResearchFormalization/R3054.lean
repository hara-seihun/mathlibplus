import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3054

open scoped BigOperators

noncomputable section

abbrev SignCube (n : ℕ) :=
  {x : Fin n → ℤ // ∀ j, x j = (-1 : ℤ) ∨ x j = 1}

/-- The root-coordinate affine class, including its coefficient data and pointwise function. -/
def rootCoordinateAffineClass {n : ℕ} (i : Fin n)
    (g : SignCube n → ℝ) : Prop :=
  ∃ c : ℝ, ∃ a : {j : Fin n // j ≠ i} → ℝ,
    |c| + (∑ j, |a j|) ≤ 1 ∧
      ∀ x, g x = c + ∑ j, a j * (x.1 j : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.R3054
