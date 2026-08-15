import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch01a000d9

/-- The finite color-weighted exponential product described by the packet. -/
noncomputable def finiteScarweavePartition
    (L C : ℕ) (n : Fin L → ℕ) (π : Fin L → Fin C → ℝ) (z : ℂ) : ℂ :=
  ∏ l : Fin L, ∏ c : Fin C,
    Complex.exp ((π l c : ℂ) * z ^ n l / (n l : ℂ))

/-- Claim 9611: the finite normalized partition has the color-weighted form. -/
def normalizedScarweavePartitionFormula : Prop :=
  ∀ (L C : ℕ) (n : Fin L → ℕ) (π : Fin L → Fin C → ℝ) (z : ℂ),
    (∀ l, 0 < n l) →
    (∀ l, ∑ c : Fin C, π l c = 1) →
    finiteScarweavePartition L C n π z =
      ∏ l : Fin L,
        Complex.exp
          (∑ c : Fin C,
            ((π l c : ℂ) * z ^ n l / (n l : ℂ)))

/-- Claim 9612: normalization removes color allocations, and the all-load
cycle-index product is the geometric generating function in its disk of
convergence. -/
def normalizedColorDataAreInvisible : Prop :=
  (∀ (L C : ℕ) (n : Fin L → ℕ) (π : Fin L → Fin C → ℝ) (z : ℂ),
      (∀ l, 0 < n l) →
      (∀ l, ∑ c : Fin C, π l c = 1) →
      finiteScarweavePartition L C n π z =
        ∏ l : Fin L, Complex.exp (z ^ n l / (n l : ℂ))) ∧
    (∀ z : ℂ, ‖z‖ < 1 →
      (∏' k : ℕ, Complex.exp (z ^ (k + 1) / ((k + 1 : ℕ) : ℂ))) =
        1 / (1 - z))

end MathlibPlus.Open.ResearchFormalizationBatch01a000d9
