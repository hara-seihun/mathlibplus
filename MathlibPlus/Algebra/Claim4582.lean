import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 4582: the completed-Bezout packet uses factorial-scaled moments
`h j = m j / (2j)!`.  The definition is kept local so the normalization
convention is recorded without introducing an unreviewed reusable object.
-/
theorem factorialMomentNormalization_claim4582 (m : ℕ → ℝ) :
    let h : ℕ → ℝ := fun j => m j / (Nat.factorial (2 * j) : ℝ)
    ∀ j : ℕ, h j = m j / (Nat.factorial (2 * j) : ℝ) := by
  dsimp
  intro j
  rfl

end MathlibPlus.Algebra
