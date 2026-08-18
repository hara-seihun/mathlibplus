import Mathlib

namespace MathlibPlus.Open.Analysis.Entire

/-- Every iterated derivative of a transcendental entire function of order
strictly below one has infinitely many zeros. -/
def transcendentalOrderLTOne_iteratedDeriv_infinite_zeros_claim609 : Prop :=
  ∀ F : ℂ → ℂ,
    Differentiable ℂ F →
      (∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
        ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧
          ∀ z : ℂ, R ≤ ‖z‖ →
            ‖F z‖ ≤ Real.exp (C * Real.rpow ‖z‖ ρ)) →
      (¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, P.eval z = F z) →
      ∀ m : ℕ, Set.Infinite {z : ℂ | iteratedDeriv m F z = 0}

end MathlibPlus.Open.Analysis.Entire
