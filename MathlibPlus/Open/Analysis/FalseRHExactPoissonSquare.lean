import Mathlib

namespace MathlibPlus.Open.Analysis

/--
False-RH nearest-shell data force the exact Poisson-square exponential growth
claimed in the admitted statement.  The nearest-shell data are supplied
explicitly so the carrier and the error estimate are part of the proposition.
-/
def falseRHForcesExactPoissonSquareExponentialGrowth
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → ℂ) (r q : ℝ) (m : ι → ℕ) (ω : ι → ℂ)
    (ε : ℕ → ℂ) (C : ℝ) : Prop :=
  (0 < r ∧ r < q ∧ q < 1 ∧
      (∀ j, 0 < m j) ∧
      Function.Injective ω ∧
      (∀ j, ‖ω j‖ = 1) ∧
      (∀ j, ∃ k, ω k = star (ω j)) ∧
      0 < ∑ j, (m j : ℝ) ^ 2 ∧
      (∀ n, ‖ε n‖ ≤ C * (r / q) ^ n) ∧
      (∀ n, S n =
        ((r : ℂ)⁻¹) ^ n *
          (∑ j, (m j : ℂ) * (ω j ^ n) + ε n))) →
    let C₀ : ℝ := ∑ j, (m j : ℝ) ^ 2
    let Q_f : ℝ → ℝ := fun x =>
      Real.exp (-x) *
        ∑' n : ℕ,
          if 1 ≤ n then
            ‖S n‖ ^ 2 * x ^ n / (Nat.factorial n : ℝ)
          else
            0
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ =>
          Q_f x / (C₀ * Real.exp (x * ((r⁻¹) ^ 2 - 1))) - 1)
        =O[Filter.atTop] (fun x : ℝ => Real.exp (-c * x))

end MathlibPlus.Open.Analysis
