import MathlibPlus.Analysis.Claim44229

namespace MathlibPlus.Open.Research.R2914DepthOneArea

/-- Claim 44228: the two exact depth-one Boolean-tree mixture areas and their
midpoint gap. -/
def claim44228 : Prop :=
  let O₁ : Fin 2 → ℚ := ![1, 0]
  let O₂ : Fin 2 → ℚ := ![0, 1]
  let A : (Fin 2 → ℚ) → ℚ := fun u =>
    min (u 0 ^ 2 + 2 * (u 1) ^ 2)
      (2 * (u 0) ^ 2 + (u 1) ^ 2)
  let f : Fin 2 → ℚ := (3 / 5 : ℚ) • O₁ + (2 / 5 : ℚ) • O₂
  let g : Fin 2 → ℚ := (2 / 5 : ℚ) • O₁ + (3 / 5 : ℚ) • O₂
  let h : Fin 2 → ℚ := (1 / 2 : ℚ) • (f + g)
  A f = 17 / 25 ∧ A g = 17 / 25 ∧ A h = 3 / 4 ∧
    A h - A f = 7 / 100

/-- Claim 44230: the same witness lies within the unit depth-one area bound,
while refuting only the endpoint-max merge guarantee. -/
def claim44230 : Prop :=
  let O₁ : Fin 2 → ℚ := ![1, 0]
  let O₂ : Fin 2 → ℚ := ![0, 1]
  let A : (Fin 2 → ℚ) → ℚ := fun u =>
    min (u 0 ^ 2 + 2 * (u 1) ^ 2)
      (2 * (u 0) ^ 2 + (u 1) ^ 2)
  let f : Fin 2 → ℚ := (3 / 5 : ℚ) • O₁ + (2 / 5 : ℚ) • O₂
  let g : Fin 2 → ℚ := (2 / 5 : ℚ) • O₁ + (3 / 5 : ℚ) • O₂
  let h : Fin 2 → ℚ := (1 / 2 : ℚ) • (f + g)
  A f = 17 / 25 ∧ A g = 17 / 25 ∧ A h = 3 / 4 ∧
    A f ≤ 1 ∧ A g ≤ 1 ∧ A h ≤ 1 ∧
      ¬ (∀ t : ℚ, 0 ≤ t → t ≤ 1 →
        A (t • f + (1 - t) • g) ≤ max (A f) (A g))

end MathlibPlus.Open.Research.R2914DepthOneArea
