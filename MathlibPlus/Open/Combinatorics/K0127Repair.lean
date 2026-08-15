import Mathlib

namespace MathlibPlus.Open.Combinatorics.K0127

def claim8928 : Prop :=
  let b : ℝ := Real.pi / 2
  let rho : ℝ → ℝ := fun z =>
    2 * ∫ u in (0 : ℝ)..1,
      Set.indicator (Set.Ioo (0 : ℝ) (b / u)) (fun _ => (1 : ℝ)) z /
        (Real.pi * Real.sqrt ((b / u) ^ 2 - z ^ 2))
  ∀ s : ℝ, 0 < s →
    (∫ z in Set.Ici (0 : ℝ), rho z / (s + z ^ 2)) =
      (Real.sqrt (s + b ^ 2) - b) / Real.rpow s (3 / 2 : ℝ) ∧
        (Real.sqrt (s + b ^ 2) - b) / Real.rpow s (3 / 2 : ℝ) =
          1 / (Real.sqrt s * (Real.sqrt (s + b ^ 2) + b))

def claim8935 : Prop :=
  let b : ℝ := Real.pi / 2
  let rho : ℝ → ℝ := fun z =>
    2 * ∫ u in (0 : ℝ)..1,
      Set.indicator (Set.Ioo (0 : ℝ) (b / u)) (fun _ => (1 : ℝ)) z /
        (Real.pi * Real.sqrt ((b / u) ^ 2 - z ^ 2))
  let tail : ℝ → ℝ := fun z => ∫ y in Set.Ici z, rho y
  ∀ z : ℝ,
    (0 < z ∧ z < b →
      tail z = b⁻¹ *
        (Real.pi / 2 - Real.arcsin (z / b) +
          (z / b) / (1 + Real.sqrt (1 - (z / b) ^ 2)))) ∧
    (b ≤ z → tail z = 1 / z)

end MathlibPlus.Open.Combinatorics.K0127
