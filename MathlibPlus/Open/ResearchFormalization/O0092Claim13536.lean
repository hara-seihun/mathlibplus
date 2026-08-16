import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0092

noncomputable section

/-- The split factor space from the reviewed separation-rank statement. -/
def splitFactor (f : ℝ → ℂ) : Prop :=
  ∃ a b c : ℂ, ∀ U : ℝ,
    f U = a + b * (Real.cosh U : ℂ) + c * (Real.sinh U : ℂ)

/-- The compact factor space from the reviewed separation-rank statement. -/
def compactFactor (f : ℝ → ℂ) : Prop :=
  ∃ a b c : ℂ, ∀ Φ : ℝ,
    f Φ = a + b * (Real.cos Φ : ℂ) + c * (Real.sin Φ : ℂ)

/-- A separated representation with exactly `r` displayed summands. -/
def hasSeparatedRepresentation (R : ℝ → ℝ → ℂ) (r : ℕ) : Prop :=
  ∃ f : Fin r → (ℝ → ℂ), ∃ g : Fin r → (ℝ → ℂ),
    (∀ i, splitFactor (f i)) ∧
      (∀ i, compactFactor (g i)) ∧
        ∀ U Φ : ℝ,
          R U Φ = ∑ i : Fin r, f i U * g i Φ

/-- Least separated width, stated without introducing a function-space carrier. -/
def separationRankExactly (R : ℝ → ℝ → ℂ) (r : ℕ) : Prop :=
  hasSeparatedRepresentation R r ∧
    ∀ q : ℕ, hasSeparatedRepresentation R q → r ≤ q

/-- The finite-heat character row with `d = 2 + x`. -/
def targetRow (x : ℝ) (σ κ : ℂ) : ℝ → ℝ → ℂ :=
  fun U Φ =>
    (2 + x : ℂ) * (Real.cosh U : ℂ) - 2 * (Real.cos Φ : ℂ) +
      σ * κ * (Real.sinh U : ℂ) * (Real.sin Φ : ℂ)

/-- Its coefficient matrix in the fixed split and compact bases. -/
def targetCoefficientMatrix (x : ℝ) (σ κ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -2, 0; (2 + x : ℂ), 0, 0; 0, 0, σ * κ]

/-- Full coefficient-matrix rank in dimension three, expressed by its determinant. -/
def coefficientMatrixFullRank (M : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  Matrix.det M ≠ 0

/--
Claim 13536.  The physical interval is part of the rank-three statement:
removing it permits the exact choice `x = -2`, for which the coefficient
matrix loses full rank even at nonzero coupling.
-/
def sourceDomainPremiseEssential : Prop :=
  (∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
    ∀ (σ : ℂ), (σ = 1 ∨ σ = -1) →
      ∀ κ : ℂ, κ ≠ 0 →
        (2 + x : ℝ) ≠ 0 ∧
          separationRankExactly (targetRow x σ κ) 3 ∧
          (Matrix.det (targetCoefficientMatrix x σ κ) =
            2 * σ * (2 + x : ℂ) * κ) ∧
          coefficientMatrixFullRank (targetCoefficientMatrix x σ κ)) ∧
  (∀ (σ : ℂ) (κ : ℂ), κ ≠ 0 → (σ = 1 ∨ σ = -1) →
    Matrix.det (targetCoefficientMatrix (-2) σ κ) = 0 ∧
      ¬ coefficientMatrixFullRank (targetCoefficientMatrix (-2) σ κ) ∧
      ¬ separationRankExactly (targetRow (-2) σ κ) 3) ∧
  (∀ (x : ℝ) (σ κ : ℂ), (σ = 1 ∨ σ = -1) → κ ≠ 0 →
    (separationRankExactly (targetRow x σ κ) 3 ↔
      coefficientMatrixFullRank (targetCoefficientMatrix x σ κ)))

end

end MathlibPlus.Open.ResearchFormalization.O0092
