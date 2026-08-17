import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim24489

private def interiorGap (α : Fin 27 → ℝ) (i : Fin 27) : ℝ :=
  4 - α i

private def interiorGapMoment (α : Fin 27 → ℝ) (k : Fin 5) : ℝ :=
  ∑ i : Fin 27, (interiorGap α i) ^ k.1

private def interiorGapMoments (α : Fin 27 → ℝ) : Fin 5 → ℝ :=
  interiorGapMoment α

private def newtonSum (δ : ℝ) (α : Fin 27 → ℝ) (k : ℕ) : ℝ :=
  (4 + δ) ^ k + ∑ i : Fin 27, (α i) ^ k

private def hankel3 (m : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => m ⟨i.1 + j.1, by omega⟩

private def schurDenominator (A B x : ℝ) : ℝ :=
  27 * (B - x ^ 2) - (A + x) ^ 2

private def schurNumerator (A B C x : ℝ) : ℝ :=
  27 * (C + x ^ 3) ^ 2 -
    2 * (A + x) * (B - x ^ 2) * (C + x ^ 3) +
    (B - x ^ 2) ^ 3

private noncomputable def p4LowerBound
    (S p₂ p₃ A B C x : ℝ) : ℝ :=
  schurNumerator A B C x / schurDenominator A B x -
    7168 + 256 * S - 96 * p₂ + 16 * p₃ + x ^ 4

private def derivativeP (A B C x : ℝ) : ℝ :=
  A * B - 27 * C + (2 * A ^ 2 - 53 * B) * x +
    3 * A * x ^ 2 + 28 * x ^ 3

private def derivativeQ (A B C x : ℝ) : ℝ :=
  B ^ 2 - A * C + (A * B - 28 * C) * x +
    (A ^ 2 - 28 * B) * x ^ 2

/-- The full Schur lower-bound function, including its δ⁴ correction, has
    the displayed factored derivative. -/
def claim24489 : Prop :=
  ∀ (δ : ℝ) (α : Fin 27 → ℝ),
    0 < δ →
    (∀ i : Fin 27, 0 < α i ∧ α i < 4) →
    schurDenominator
        (112 - newtonSum δ α 1)
        (448 - 8 * newtonSum δ α 1 + newtonSum δ α 2)
        δ ≠ 0 →
    let S := newtonSum δ α 1
    let p₂ := newtonSum δ α 2
    let p₃ := newtonSum δ α 3
    let A := 112 - S
    let B := 448 - 8 * S + p₂
    let C := 1792 - 48 * S + 12 * p₂ - p₃
    deriv (fun x : ℝ => p4LowerBound S p₂ p₃ A B C x) δ *
        (27 * interiorGapMoments α 2 -
          (interiorGapMoments α 1) ^ 2) ^ 2 =
      2 * derivativeP A B C δ * derivativeQ A B C δ

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim24489
