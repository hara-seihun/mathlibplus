import MathlibPlus.Open.ResearchBatch.R3642

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch.R3642

noncomputable def checkerboardThetaShellIncrement_claim51120 : Prop :=
  let α : ℝ := 1 / 4
  let c : (ℕ → ℝ) → ℕ → ℝ :=
    fun moments j => (-1 : ℝ) ^ j * moments j
  let r : (ℕ → ℝ) → ℕ → ℝ :=
    fun moments j =>
      ((j + 1 : ℕ) : ℝ) * (c moments j + α * c moments (j + 1))
  let b : (ℕ → ℝ) → ℕ → ℕ → ℝ :=
    fun moments i j =>
      ∑ ℓ ∈ Finset.range (i + j + 2),
        ∑ k ∈ Finset.range (i + j + 2),
          if ℓ + k = i + j + 1 ∧
              ℓ < k ∧ ℓ ≤ i ∧ ℓ ≤ j ∧ i < k ∧ j < k then
            -((k - ℓ : ℕ) : ℝ) * c moments ℓ * c moments k
          else 0
  let K : (ℕ → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
    fun moments i j =>
      (1 / 2 : ℝ) * r moments (i.val + j.val) +
        α ^ 2 * b moments i.val j.val +
        α *
          ((if i.val = 0 then 0 else b moments (i.val - 1) j.val) +
            (if j.val = 0 then 0 else b moments i.val (j.val - 1))) +
        (if i.val = 0 ∨ j.val = 0 then 0
          else b moments (i.val - 1) (j.val - 1)) -
        α * c moments i.val * c moments j.val
  let m1 : ℕ → ℝ := fun j => thetaShellMoment 1 j
  let m12 : ℕ → ℝ :=
    fun j => thetaShellMoment 1 j + thetaShellMoment 2 j
  let Δ : Matrix (Fin 3) (Fin 3) ℝ := K m12 - K m1
  Matrix.det Δ < 0 ∧
    ∀ d : Fin 3 → ℝ,
      (∀ i, d i = (-1 : ℝ) ∨ d i = 1) →
        let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal d
        Matrix.det (D * Δ * D) = Matrix.det Δ ∧
          Matrix.det (D * Δ * D) < 0 ∧
            ¬ Matrix.PosSemidef (D * Δ * D)

end MathlibPlus.Open.ResearchBatch.R3642
