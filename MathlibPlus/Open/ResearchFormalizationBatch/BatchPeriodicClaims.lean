import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

private def purePeriodicBinary (p : ℕ) (e : ℕ → ℕ) : Prop :=
  0 < p ∧
  (∀ d : ℕ, 1 ≤ d → e d = 0 ∨ e d = 1) ∧
  (∃ r s : ℕ, 1 ≤ r ∧ r ≤ p ∧ 1 ≤ s ∧ s ≤ p ∧ e r ≠ e s) ∧
  (∀ k r : ℕ, 1 ≤ r → r ≤ p → e (k * p + r) = e r) ∧
  (∀ q : ℕ, 0 < q → q < p →
    ¬ (∀ d : ℕ, 1 ≤ d → e (d + q) = e d))

private def periodicM (p : ℕ) : ℝ := (2 : ℝ) ^ p - 1

private def periodicC (p : ℕ) (e : ℕ → ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 p, (e r : ℝ) * (2 : ℝ) ^ (p - r)

private def periodicJ (p : ℕ) (e : ℕ → ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 p, (r : ℝ) * (e r : ℝ) * (2 : ℝ) ^ (p - r)

private def periodicA (e : ℕ → ℕ) : ℝ :=
  ∑' d : ℕ, if 1 ≤ d then (e d : ℝ) / (2 : ℝ) ^ d else 0

private def periodicB (e : ℕ → ℕ) : ℝ :=
  ∑' d : ℕ, if 1 ≤ d then (d : ℝ) * (e d : ℝ) / (2 : ℝ) ^ d else 0

/-- Exact offset sums and the affine-target denominator formula for pure periods. -/
def claim_45288 : Prop :=
  ∀ (p : ℕ) (e : ℕ → ℕ) (n : ℕ),
    purePeriodicBinary p e →
    let M := periodicM p
    let C := periodicC p e
    let J := periodicJ p e
    let A := periodicA e
    let B := periodicB e
    A = C / M ∧
      B = (M * J + (p : ℝ) * C) / M ^ 2 ∧
      ((n : ℝ) = (n : ℝ) * A + B →
        (n : ℝ) = (M * J + (p : ℝ) * C) / (M * (M - C)) ∧
          (n : ℝ) = B / (1 - A))

/-- No nonconstant pure period gives an integral affine target. -/
def claim_45289 : Prop :=
  (∀ (p : ℕ) (e : ℕ → ℕ),
    purePeriodicBinary p e →
    ¬ ∃ n : ℤ, (n : ℝ) = periodicB e / (1 - periodicA e)) ∧
  (∀ (p : ℕ) (e : ℕ → ℕ),
    0 < p →
    (∀ d : ℕ, 1 ≤ d → e d = 0) →
      periodicA e = 0 ∧ periodicB e = 0) ∧
  (∀ (p : ℕ) (e : ℕ → ℕ),
    0 < p →
    (∀ d : ℕ, 1 ≤ d → e d = 1) →
      1 - periodicA e = 0)

end MathlibPlus.Open.ResearchFormalizationBatch
