import Mathlib

namespace MathlibPlus.Open.MomentGeometry.ResearchFormalizationR0196

open scoped BigOperators

private def cTwoDeterminant (h : Fin 4 → ℝ) : ℝ :=
  3 * h 0 ^ 2 * h 1 * h 3 + h 0 * h 1 ^ 2 * h 2 -
    4 * h 0 ^ 2 * h 2 ^ 2

private def strictlyTotallyPositiveCell {n : ℕ}
    (B : Matrix (Fin n) (Fin 4) ℝ) : Prop :=
  ∀ r : ℕ, 0 < r →
    ∀ rows : Fin r → Fin n, StrictMono rows →
      ∀ cols : Fin r → Fin 4, StrictMono cols →
        0 < Matrix.det (fun i j : Fin r => B (rows i) (cols j))

/-- The degree-two exterior coordinates of an `n` by `4` cell matrix: an
ordered pair of rows and an ordered pair of columns, rather than a maximal
minor whose degree varies with `n`. -/
private def degreeTwoIndex (n : ℕ) : Type :=
  {rows : Fin 2 → Fin n // StrictMono rows} ×
    {cols : Fin 2 → Fin 4 // StrictMono cols}

private def degreeTwoPluckerData {n : ℕ}
    (B : Matrix (Fin n) (Fin 4) ℝ) : degreeTwoIndex n → ℝ :=
  fun I =>
    Matrix.det (fun i j : Fin 2 => B (I.1.1 i) (I.2.1 j))

private def positivePluckerCone (n : ℕ) : Set (degreeTwoIndex n → ℝ) :=
  {p | ∀ I, 0 ≤ p I}

private def exteriorIntertwiner : Type :=
  ∀ n : ℕ, (degreeTwoIndex n → ℝ) →ₗ[ℝ] ℝ

private def rowSumMoments {n : ℕ}
    (B : Matrix (Fin n) (Fin 4) ℝ) : Fin 4 → ℝ :=
  fun j => ∑ i : Fin n, B i j

/-- No dimension-uniform linear degree-two exterior/Plücker functional is
nonnegative on the positive Plücker cone and agrees with the quadratic `C₂`
determinant of row-sum moments on every strictly totally positive cell. -/
def claim18723_noUniversalExteriorPositiveC2Intertwiner : Prop :=
  ¬ ∃ L : exteriorIntertwiner,
      (∀ n : ℕ, ∀ p : degreeTwoIndex n → ℝ,
        p ∈ positivePluckerCone n → 0 ≤ (L n).toFun p) ∧
      (∀ n : ℕ, ∀ B : Matrix (Fin n) (Fin 4) ℝ,
        strictlyTotallyPositiveCell B →
          (L n).toFun (degreeTwoPluckerData B) =
            cTwoDeterminant (rowSumMoments B))

end MathlibPlus.Open.MomentGeometry.ResearchFormalizationR0196
