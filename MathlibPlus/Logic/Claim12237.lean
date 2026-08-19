import Mathlib

namespace MathlibPlus.Logic

/--
The exact backward-persistence contradiction in Claim 12237.  `C` forces
`Good` on the stated left-neighbourhood of zero, while `C 0` forces `C` on a
nonzero backward interval; failure of `Good` at every negative parameter then
rules out `C 0`.
-/
def backwardPersistenceContradiction_claim12237 : Prop :=
  ∀ (Good C : ℝ → Prop) (η : ℝ),
    0 < η →
    (∀ τ : ℝ, -η < τ → τ ≤ 0 → C τ → Good τ) →
    (∃ δ : ℝ, 0 < δ ∧
      ∀ τ : ℝ, -δ < τ → τ ≤ 0 → C 0 → C τ) →
    (∀ τ : ℝ, τ < 0 → ¬ Good τ) →
    ¬ C 0

end MathlibPlus.Logic
