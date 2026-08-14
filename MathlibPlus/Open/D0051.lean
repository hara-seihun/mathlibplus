import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.D0051

open MeasureTheory

/-- The Xi-derived generating function in the even variable. -/
def claim4759
    (Xi G : ℂ → ℂ) (a : ℕ → ℂ) (m : ℕ → ℝ) : Prop :=
  (∀ s : ℂ, Xi (-s) = Xi s) ∧
    (∀ z : ℂ, G z = Xi (Complex.sqrt (-z))) ∧
    (∀ z : ℂ, HasSum (fun n : ℕ => a n * z ^ n) (G z)) ∧
    (∀ n : ℕ, a n = (m n : ℂ) / (Nat.factorial (2 * n) : ℂ))

/-- The completed-theta measure and its even moments. -/
def claim4760
    (Φ : ℝ → ℝ) (ν : Measure ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ s : Set ℝ, MeasurableSet s →
    ν s = ∫⁻ u in s ∩ Set.Ici (0 : ℝ), ENNReal.ofReal (2 * Φ u) ∂MeasureTheory.volume) ∧
    (∀ n : ℕ, m n = ∫ u in Set.Ici (0 : ℝ), u ^ (2 * n) ∂ν)

/-- Positivity of all moments and normalized coefficients. -/
def claim4762
    (ν : Measure ℝ) (m a : ℕ → ℝ) : Prop :=
  (0 < ν (Set.Ioi (0 : ℝ)) ∧
      (∀ n : ℕ, Integrable (fun u : ℝ => u ^ (2 * n))
        (ν.restrict (Set.Ici (0 : ℝ)))) ∧
      (∀ n : ℕ, m n = ∫ u in Set.Ici (0 : ℝ), u ^ (2 * n) ∂ν) ∧
      (∀ n : ℕ, a n = m n / (Nat.factorial (2 * n) : ℝ))) →
    ∀ n : ℕ, 0 < m n ∧ 0 < a n

/-- The differential-operator representation of the polynomial family. -/
def claim4766
    (G : ℝ → ℝ) (P : ℕ → ℕ → ℝ → ℝ) : Prop :=
  let D : (ℝ → ℝ) → (ℝ → ℝ) := fun f x => deriv f x
  let T : ℝ → (ℝ → ℝ) → (ℝ → ℝ) := fun x f t => f t + x * D f t
  ∀ (d n : ℕ) (x : ℝ),
    P d n x =
      ((T x)^[d] (D^[n] G)) 0

end MathlibPlus.Open.D0051
