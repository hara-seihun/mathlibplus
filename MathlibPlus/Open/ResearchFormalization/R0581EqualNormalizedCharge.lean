import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0581EqualNormalizedCharge

noncomputable section

structure ThreeDisjointMinimumFamily (V : Type*) [DecidableEq V] where
  family : Finset (Finset V)
  M₁ : Finset V
  M₂ : Finset V
  M₃ : Finset V
  valid :
    M₁ ∈ family ∧ M₂ ∈ family ∧ M₃ ∈ family ∧
      M₁.Nonempty ∧ M₂.Nonempty ∧ M₃.Nonempty ∧
      (∀ x, x ∈ M₁ → x ∉ M₂) ∧
      (∀ x, x ∈ M₁ → x ∉ M₃) ∧
      (∀ x, x ∈ M₂ → x ∉ M₃) ∧
      (∀ A, A ∈ family → ∀ B, B ∈ family → A ∪ B ∈ family) ∧
      (∀ A, A ∈ family → A.Nonempty →
        ((∀ B, B ∈ family → B.Nonempty → B ⊆ A → A ⊆ B) ↔
          A = M₁ ∨ A = M₂ ∨ A = M₃))

/-- The exact per-member equal-block normalized charge.  The member argument
is a subtype of the actual family, so the charge is not defined on an
unconstrained ambient Finset. -/
def normalizedBlockCharge_claim22953 {V : Type*} [DecidableEq V]
    (C : ThreeDisjointMinimumFamily V)
    (S : {A : Finset V // A ∈ C.family}) : ℚ :=
  2 * ((S.1 ∩ C.M₁).card : ℚ) / (C.M₁.card : ℚ) +
      2 * ((S.1 ∩ C.M₂).card : ℚ) / (C.M₂.card : ℚ) +
      2 * ((S.1 ∩ C.M₃).card : ℚ) / (C.M₃.card : ℚ) - 3

end

end MathlibPlus.Open.ResearchFormalization.R0581EqualNormalizedCharge
