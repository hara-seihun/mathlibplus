import Mathlib

namespace MathlibPlus.Open

noncomputable def batchRisingFactorial (x : ℝ) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun u => x + (u : ℝ))

noncomputable def batchGammaMoment (α : ℝ) (n : ℕ) : ℝ :=
  batchRisingFactorial α n

noncomputable def batchBezoutH (α : ℝ) (j : ℕ) : ℝ :=
  batchRisingFactorial α j / (Nat.factorial (2 * j) : ℝ)

noncomputable def batchCompletedBezout (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    Finset.sum (Finset.range (Nat.min i.val j.val + 1)) (fun a =>
      ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) *
        batchBezoutH α a *
        batchBezoutH α (i.val + j.val + 1 - a))

noncomputable def batchPivotDenominator (j : ℕ) : ℝ :=
  2 * Finset.prod (Finset.range j) (fun u =>
    2 * (4 * (u : ℝ) + 1) * (4 * (u : ℝ) + 3) ^ 2 *
      (4 * (u : ℝ) + 5))

noncomputable def batchGammaPivot (α : ℝ) (j : ℕ) : ℝ :=
  (batchRisingFactorial α (j + 1) *
      Finset.prod (Finset.range j) (fun u => 2 * α - (2 * (u : ℝ) + 1))) /
    batchPivotDenominator j

noncomputable def batchLowerFactor (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if j.val ≤ i.val then
      batchRisingFactorial (α + (j.val : ℝ) + 1) (i.val - j.val) /
          ((4 : ℝ) ^ (i.val - j.val) *
            (Nat.factorial (i.val - j.val) : ℝ) *
            batchRisingFactorial
              (2 * (j.val : ℝ) + (3 / 2 : ℝ)) (i.val - j.val))
    else
      0

noncomputable def batchDiagonalPivot (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then batchGammaPivot α i.val else 0

def batchLeadingBezoutPositive (α : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N → 0 < Matrix.det (batchCompletedBezout α n)

def claim10514_varianceCoordinateFiniteRankChamber : Prop :=
  ∀ α : ℝ, 0 < α →
    let m₀ := batchGammaMoment α 0
    let m₁ := batchGammaMoment α 1
    let m₂ := batchGammaMoment α 2
    let V := m₀ * m₂ / m₁ ^ 2
    V = m₀ * m₂ / m₁ ^ 2 ∧
      V = 1 + 1 / α ∧
        ∀ N : ℕ, 2 ≤ N →
          (batchLeadingBezoutPositive α N ↔
            1 < V ∧ V < 1 + 2 / (2 * (N : ℝ) - 3))

def claim10520_allRankLDLFactorization : Prop :=
  ∀ α : ℝ, ∀ N : ℕ,
    batchCompletedBezout α N =
        (batchLowerFactor α N * batchDiagonalPivot α N) *
          Matrix.transpose (batchLowerFactor α N) ∧
      (∀ i j : Fin N, j.val > i.val →
        batchLowerFactor α N i j = 0) ∧
      (∀ i : Fin N, batchLowerFactor α N i i = 1)

noncomputable def batchMomentKernel (α : ℝ) (p q : ℕ) : ℝ :=
  batchGammaMoment α (p + q)

def batchStrictlyTotallyPositiveMomentKernel (α : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    ∀ p q : Fin r → ℕ,
      StrictMono p → StrictMono q →
        0 < Matrix.det (fun i j : Fin r =>
          batchMomentKernel α (p i) (q j))

def claim10522_firstNegativePivotPositiveIntegerShape : Prop :=
  ∀ a : ℕ, 0 < a →
    (∀ j : ℕ, j ≤ a → 0 < batchGammaPivot (a : ℝ) j) ∧
      batchGammaPivot (a : ℝ) (a + 1) < 0 ∧
      0 < Matrix.det (batchCompletedBezout (a : ℝ) (a + 1)) ∧
      Matrix.det (batchCompletedBezout (a : ℝ) (a + 2)) < 0 ∧
      batchStrictlyTotallyPositiveMomentKernel (a : ℝ)

end MathlibPlus.Open
