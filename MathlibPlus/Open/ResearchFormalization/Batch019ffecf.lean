import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffecf

/-- Claim 2316: the stated uniform power-sum estimate. -/
def claim_2316 : Prop :=
  ∀ Y : ℝ, 0 ≤ Y → Y < (1 / 2 : ℝ) →
    ∃ C_Y : ℝ,
      ∀ y : ℝ, -Y ≤ y → y ≤ Y →
        ∀ N : ℕ, 1 ≤ N →
          (Finset.sum (Finset.Icc 1 N)
              (fun n => Real.rpow (n : ℝ) (y - (1 / 2 : ℝ))))
            ≤ C_Y * Real.rpow (N : ℝ) (y + (1 / 2 : ℝ))

/-- Claim 2376: the left-exterior compensation identity and its Dini numerator. -/
def claim_2376 : Prop :=
  ∀ A L z : ℝ,
    -(MeasureTheory.integral (volume.restrict (Set.Iic (0 : ℝ)))
        (fun x => A * Real.exp (x / 2) * Real.cos (z * (x - L / 2))))
      = A * (z * Real.sin (L * z / 2) - (1 / 2 : ℝ) * Real.cos (L * z / 2)) /
          (z ^ 2 + (1 / 4 : ℝ))

/-- Claim 2377: every complex zero of the displayed Dini numerator is real and simple. -/
def claim_2377 : Prop :=
  ∀ L : ℝ, 0 < L →
    let D : ℂ → ℂ := fun z =>
      z * Complex.sin ((L : ℂ) * z / 2) - (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z / 2)
    ∀ z : ℂ, D z = 0 → z.im = 0 ∧ deriv D z ≠ 0

end MathlibPlus.Open.ResearchFormalization.Batch019ffecf
