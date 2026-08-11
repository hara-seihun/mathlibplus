import Mathlib

namespace MathlibPlus.Open.Algebra

/-!
Formalization of admitted claim 25953.  The finite interval `{0, ..., M}`
is represented by `Fin (M + 1)`, and the four indices in the functional
equation are natural numbers constrained by their sum.
-/

/-- The quadratic finite-interval functional equation from claim 25953. -/
def quadraticFiniteIntervalFunctionalEquation : Prop :=
  ∀ M : ℕ, 4 ≤ M →
    ∀ u : Fin (M + 1) → ℚ,
      (∀ j : Fin (M + 1),
        u j = u ⟨M - j.1, by omega⟩) →
      (∀ a b c d : ℕ, ∀ h : a + b + c + d = M,
        u ⟨a + b, by omega⟩ +
            u ⟨a + c, by omega⟩ +
            u ⟨a + d, by omega⟩ -
            u ⟨a, by omega⟩ -
            u ⟨b, by omega⟩ -
            u ⟨c, by omega⟩ -
            u ⟨d, by omega⟩ +
            u ⟨0, by omega⟩ = 0) →
      ∃ C lam : ℚ, ∀ j : Fin (M + 1),
        u j = C + lam * (j.1 : ℚ) * ((j.1 : ℚ) - (M : ℚ))

end MathlibPlus.Open.Algebra
