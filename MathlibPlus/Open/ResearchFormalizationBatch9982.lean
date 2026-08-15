import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch9982

open scoped BigOperators

noncomputable section

/--
The exponential change of variables sends the selected reciprocal polynomial
roots to simple, disjoint vertical progressions.  The polynomial carriers are
expanded here from the admitted definition of the family so that this node is
independent of any unavailable source module.
-/
def unitCircleRootsLiftToInfiniteCriticalLineProgressions : Prop :=
  let a : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  let D : ℕ → ℕ := fun m => 4 * m + 2
  let F : ℕ → Polynomial ℂ := fun m =>
    ∑ k ∈ Finset.range (m + 1),
      Polynomial.C (a ^ k) * Polynomial.X ^ k
  let H : ℕ → Polynomial ℂ := fun m =>
    ∑ k ∈ Finset.range (m + 1),
      Polynomial.C (a ^ k) * Polynomial.X ^ (m - k)
  let P : ℕ → Polynomial ℂ := fun m =>
    F m + Polynomial.X ^ (D m - m) * H m
  let Q : ℕ → ℚ → Polynomial ℂ := fun m τ =>
    1 + Polynomial.C (τ : ℂ) * Polynomial.X ^ (D m / 2) +
      Polynomial.X ^ D m
  let lift : ℂ → ℂ := fun s =>
    Complex.exp (-(Real.log 2 : ℂ) * (s - (1 / 2 : ℂ)))
  let period : ℂ :=
    (2 * (Real.pi : ℂ) / (Real.log 2 : ℂ)) * Complex.I
  ∀ m : ℕ, 1 ≤ m →
    ∃ τ : ℚ,
      (-1 : ℚ) < τ ∧ τ < 1 ∧
      IsCoprime (P m) (Q m τ) ∧
      (∀ s x : ℂ, lift s = x →
        ‖x‖ = Real.exp (-Real.log 2 * (s.re - (1 / 2 : ℝ))) ∧
        (‖x‖ = 1 ↔ s.re = (1 / 2 : ℝ))) ∧
      Disjoint
        {s : ℂ | Polynomial.eval (lift s) (P m) = 0}
        {s : ℂ | Polynomial.eval (lift s) (Q m τ) = 0} ∧
      (∀ x₀ : ℂ,
        Polynomial.IsRoot (P m) x₀ →
        Polynomial.eval x₀ (Polynomial.derivative (P m)) ≠ 0 →
        ∃ s₀ : ℂ,
          lift s₀ = x₀ ∧
          ‖x₀‖ = 1 ∧
          s₀.re = (1 / 2 : ℝ) ∧
          {s : ℂ | lift s = x₀} =
            Set.range (fun n : ℤ => s₀ + (n : ℂ) * period) ∧
          Set.Infinite {s : ℂ | lift s = x₀} ∧
          (∀ s : ℂ, lift s = x₀ →
            Polynomial.eval (lift s) (P m) = 0 ∧
            deriv (fun z : ℂ => Polynomial.eval (lift z) (P m)) s ≠ 0)) ∧
      (∀ x₀ : ℂ,
        Polynomial.IsRoot (Q m τ) x₀ →
        Polynomial.eval x₀ (Polynomial.derivative (Q m τ)) ≠ 0 →
        ∃ s₀ : ℂ,
          lift s₀ = x₀ ∧
          ‖x₀‖ = 1 ∧
          s₀.re = (1 / 2 : ℝ) ∧
          {s : ℂ | lift s = x₀} =
            Set.range (fun n : ℤ => s₀ + (n : ℂ) * period) ∧
          Set.Infinite {s : ℂ | lift s = x₀} ∧
          (∀ s : ℂ, lift s = x₀ →
            Polynomial.eval (lift s) (Q m τ) = 0 ∧
            deriv (fun z : ℂ => Polynomial.eval (lift z) (Q m τ)) s ≠ 0))

end

end MathlibPlus.Open.ResearchFormalizationBatch9982
