import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

open Filter Asymptotics MeasureTheory

/-- Claim 13632: exact first-column checkerboard formula and its stated
conditional little-o consequences. -/
def claim13632 : Prop :=
  ∀ (α b : ℝ) (t : ℕ → ℝ),
    let A : ℝ := b - α * t 0
    let K : ℕ → ℝ := fun n ↦
      (b * ((n + 1 : ℕ) : ℝ) - α * (n : ℝ) * t 0) * t n
        - α * ((n + 1 : ℕ) : ℝ) * (b - α * t 0) * t (n + 1)
    let m : ℕ → ℝ := fun n ↦ K n / K (n - 1)
    (IsLittleO atTop (fun n ↦ t (n + 1) / t n) (fun _ ↦ (1 : ℝ)) ∧
        0 < A) →
      IsLittleO atTop
          (fun n ↦ K n - A * (n : ℝ) * t n)
          (fun n ↦ A * (n : ℝ) * t n) ∧
        IsLittleO atTop
          (fun n ↦
            m n - ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) *
              (t n / t (n - 1)))
          (fun n ↦
            ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) *
              (t n / t (n - 1)))

/-- Claim 13633: first-shell dominance for the explicitly displayed theta
moments, with the displayed tail estimate interpreted at infinity. -/
def claim13633 : Prop :=
  ∀ (T : ℝ → ℝ),
    IsBigO atTop
        (fun u ↦ T u - Real.exp (-Real.pi * Real.exp (2 * u)))
        (fun u ↦
          Real.exp (-Real.pi * Real.exp (2 * u)) *
            Real.exp (-3 * Real.pi * Real.exp (2 * u))) →
      let I : ℕ → ℝ := fun n ↦
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (u / 2) * T u * u ^ (2 * n)
      let t : ℕ → ℝ := fun n ↦
        2 * I n / (Nat.factorial (2 * n) : ℝ)
      let φ : ℕ → ℝ → ℝ := fun n u ↦
        (2 * n : ℝ) * Real.log u + u / 2 - Real.pi * Real.exp (2 * u)
      let J : ℕ → ℝ := fun n ↦
        ∫ u in Set.Ioi (0 : ℝ), Real.exp (φ n u)
      IsLittleO atTop (fun n ↦ I n - J n) (fun n ↦ J n)

end MathlibPlus.Open.ResearchFormalizationBatch
