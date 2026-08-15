import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization

/-- Reciprocal heat transition matrices have strictly positive minors. -/
def claim2858 : Prop :=
  ∀ (r : ℕ) (q l : Fin r → ℝ),
    StrictMono q → (∀ i, 1 < l i) → StrictMono l →
      ∀ a : ℝ,
        let U : Matrix (Fin r) (Fin r) ℝ := fun i j =>
          Real.rpow (l j) (-a) * Real.exp (-q i / l j)
        let V : Matrix (Fin r) (Fin r) ℝ := fun i j =>
          Real.rpow (l j) a * Real.exp (-q i * l j)
        let D : Matrix (Fin r) (Fin r) ℝ := fun i j =>
          if i = j then (-1 : ℝ) ^ i.1 else 0
        let B : Matrix (Fin r) (Fin r) ℝ := D * U⁻¹ * V
        U.det ≠ 0 ∧
          (∀ (k : ℕ) (I J : Fin k → Fin r),
            StrictMono I → StrictMono J →
              0 < Matrix.det (fun i j => B (I i) (J j)))

/-- The explicit three-row witness has positive Vandermonde minors but a
negative determinant in the displayed rank-two matrix. -/
def claim10563 : Prop :=
  let x : Fin 3 → ℝ := ![1, 2, 6]
  let w : Fin 3 → ℝ := ![1, 1, 5]
  let B : Matrix (Fin 3) (Fin 4) ℝ := fun n j => w n * x n ^ j.1
  let h : Fin 4 → ℝ := ![7, 33, 185, 1089]
  let C₂ : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    match (i.1, j.1) with
    | (0, 0) => h 0 * h 1
    | (0, 1) => 2 * h 0 * h 2
    | (1, 0) => 2 * h 0 * h 2
    | (1, 1) => 3 * h 0 * h 3 + h 1 * h 2
    | _ => 0
  (∀ (k : ℕ), k ≤ 3 →
      ∀ (I : Fin k → Fin 3) (J : Fin k → Fin 4),
        StrictMono I → StrictMono J →
          0 < Matrix.det (fun i j => B (I i) (J j))) ∧
    (∀ j : Fin 4, h j = ∑ n, B n j) ∧
    h = ![7, 33, 185, 1089] ∧
    Matrix.det C₂ = -15106

end MathlibPlus.Open.ResearchFormalization
