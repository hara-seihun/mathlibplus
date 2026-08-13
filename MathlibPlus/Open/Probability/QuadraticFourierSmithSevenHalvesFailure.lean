import Mathlib

namespace MathlibPlus.Open.Probability

/--
The singleton/pair Fourier mass budgets alone do not force the Smith block
objective below `7 / 2`.
-/
def quadraticFourierSmithSevenHalvesFailure : Prop :=
  let x₀ : ℚ := 29 / 99
  let x₁ : ℚ := 35 / 99
  let x₂ : ℚ := 35 / 99
  let y₀ : ℚ := 1 / 2
  let y₁ : ℚ := 1 / 2
  let X₂ := x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2
  let Y₂ := y₀ ^ 2 + y₁ ^ 2
  let mixed :=
    min (y₀ ^ 2) (2 * x₀ ^ 2) + min (y₁ ^ 2) (2 * x₀ ^ 2) +
    min (y₀ ^ 2) (2 * x₁ ^ 2) + min (y₁ ^ 2) (2 * x₁ ^ 2) +
    min (y₀ ^ 2) (2 * x₂ ^ 2) + min (y₁ ^ 2) (2 * x₂ ^ 2)
  let objective := ((x₀ + x₁ + x₂) ^ 2 + X₂) / 2 +
    ((y₀ + y₁) ^ 2 + Y₂) + mixed
  x₀ + x₁ + x₂ = 1 ∧
    y₀ + y₁ = 1 ∧
    X₂ + Y₂ = 5461 / 6534 ∧
    X₂ + Y₂ < 1 ∧
    mixed = 4388 / 3267 ∧
    objective = 2549 / 726 ∧
    objective - 7 / 2 = 4 / 363 ∧
    7 / 2 < objective

end MathlibPlus.Open.Probability
