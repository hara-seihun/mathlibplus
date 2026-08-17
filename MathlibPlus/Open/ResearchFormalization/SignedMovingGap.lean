import MathlibPlus.Open.ResearchFormalization.SignedGap

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 48277: the denominator-three recurrence, its signed affine branches,
and the fixed-time affine-state simulation interface are recorded on the exact
integer state carrier. -/
def claim_48277 : Prop := by
  exact
    (∀ (G : ℤ → ℤ),
      ((∀ j : ℤ, G (j + 1) =
          MathlibPlus.Open.ResearchFormalization.SignedGap.movingGapRecurrence j (G j)) ↔
        (∀ j : ℤ, G (j + 1) =
          2 * min (G j) (3 * (j + 3) - G j)))) ∧
    (∀ j g : ℤ,
      MathlibPlus.Open.ResearchFormalization.SignedGap.movingGapUp j g = 2 * g ∧
      MathlibPlus.Open.ResearchFormalization.SignedGap.movingGapDown j g =
        6 * (j + 3) - 2 * g) ∧
    (∀ k : ℕ, ∀ A B C D : ℤ,
      2 ≤ k → A ≠ 0 →
        ¬ ∃ (wordUp wordDown : Fin k → Bool),
          (∀ j g : ℤ,
            MathlibPlus.Open.ResearchFormalization.SignedGap.applyTargetWord k wordUp
                (MathlibPlus.Open.ResearchFormalization.SignedGap.affineStateMap
                  k A B C D j g) =
              MathlibPlus.Open.ResearchFormalization.SignedGap.affineStateMap
                k A B C D (j + 1)
                (MathlibPlus.Open.ResearchFormalization.SignedGap.movingGapUp j g)) ∧
          (∀ j g : ℤ,
            MathlibPlus.Open.ResearchFormalization.SignedGap.applyTargetWord k wordDown
                (MathlibPlus.Open.ResearchFormalization.SignedGap.affineStateMap
                  k A B C D j g) =
              MathlibPlus.Open.ResearchFormalization.SignedGap.affineStateMap
                k A B C D (j + 1)
                (MathlibPlus.Open.ResearchFormalization.SignedGap.movingGapDown j g)))

end MathlibPlus.Open.ResearchFormalization
