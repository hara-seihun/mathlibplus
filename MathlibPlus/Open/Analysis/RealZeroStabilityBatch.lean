import Mathlib

namespace MathlibPlus.Open.Analysis.RealZeroStability

/-- A closed rectangle in the complex plane. -/
def closedRectangle (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- Entire functions with real symmetry. -/
def realEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    (∀ z : ℂ, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))

/-- Local uniform convergence on compact subsets of an open neighborhood. -/
def locallyUniformlyConvergesOnNeighborhood (R : Set ℂ)
    (fcs : ℕ → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ U : Set ℂ,
    IsOpen U ∧ R ⊆ U ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ U →
        ∀ ε : ℝ, 0 < ε →
          ∃ c₀ : ℕ, ∀ c : ℕ, c ≥ c₀ → ∀ z : ℂ, z ∈ K →
            ‖fcs c z - f z‖ < ε

/-- Stability of real simple zeros on a fixed closed rectangle. -/
def realSimpleZerosStableOnRectangle : Prop :=
  ∀ (a b c d : ℝ) (fcs : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    a ≤ b → c ≤ d →
    let R : Set ℂ := closedRectangle a b c d
    (∀ n : ℕ, realEntire (fcs n)) →
    realEntire f →
    locallyUniformlyConvergesOnNeighborhood R fcs f →
    (∀ z : ℂ, z ∈ frontier R → f z ≠ 0) →
    (∀ z : ℂ, z ∈ R → f z = 0 → z.im = 0 ∧ deriv f z ≠ 0) →
    ∃ c₀ : ℕ, ∀ c : ℕ, c ≥ c₀ →
      ∀ z : ℂ, z ∈ R → fcs c z = 0 → z.im = 0 ∧ deriv (fcs c) z ≠ 0

end MathlibPlus.Open.Analysis.RealZeroStability
