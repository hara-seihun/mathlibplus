import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The Hermitian positive-semidefinite verdict is unchanged by correlation
normalization with the positive diagonal of the matrix. -/
def correlationNormalizationPreservesPSD : Prop :=
  ∀ (n : ℕ) (W : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, W i j = star (W j i)) →
    (∀ i, (W i i).im = 0 ∧ 0 < (W i i).re) →
    let normalized : Matrix (Fin n) (Fin n) ℂ := fun i j =>
      ((Real.sqrt (W i i).re)⁻¹ : ℂ) * W i j *
        ((Real.sqrt (W j j).re)⁻¹ : ℂ)
    (∀ x : Fin n → ℂ,
        0 ≤ (∑ i, ∑ j, star (x i) * W i j * x j).re) ↔
      (∀ x : Fin n → ℂ,
        0 ≤ (∑ i, ∑ j, star (x i) * normalized i j * x j).re)

/-- The diagonal similitude with entries 2 and 9/2 preserves the standard
split bilinear form with multiplier 9, while its eigenvalue moduli are not
pure of radius 3. -/
def splitSimilitudeDoesNotImplyPurity : Prop :=
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = 0 ∧ j = 0 then 2
    else if i = 1 ∧ j = 1 then (9 / 2 : ℝ)
    else 0
  let J : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0
  let isEigenvalue : ℝ → Prop := fun e =>
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ A.mulVec v = e • v
  A.transpose * J * A = (9 : ℝ) • J ∧
    isEigenvalue 2 ∧
    isEigenvalue (9 / 2 : ℝ) ∧
    (∀ e : ℝ, isEigenvalue e →
      |e| = 2 ∨ |e| = (9 / 2 : ℝ)) ∧
    (2 : ℝ) ≠ 3 ∧ (9 / 2 : ℝ) ≠ 3

end MathlibPlus.Open.ResearchFormalization
