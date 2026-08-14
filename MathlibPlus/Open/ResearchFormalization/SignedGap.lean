import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.SignedGap

/-- The two signed affine branches before the feasibility inequality is imposed. -/
def movingGapUp (j g : ℤ) : ℤ := 2 * g

def movingGapDown (j g : ℤ) : ℤ := 6 * (j + 3) - 2 * g

def movingGapRecurrence (j g : ℤ) : ℤ :=
  2 * min g (3 * (j + 3) - g)

def targetUp (state : ℤ × ℤ) : ℤ × ℤ :=
  (state.1 + 1, 2 * state.2)

def targetDown (state : ℤ × ℤ) : ℤ × ℤ :=
  (state.1 + 1, 6 * (state.1 + 3) - 2 * state.2)

def affineStateMap (k : ℕ) (A B C D j g : ℤ) : ℤ × ℤ :=
  ((k : ℤ) * j + B, A * g + C * j + D)

/-- Applying a word of exactly `k` target branch steps. -/
def applyTargetWord : (k : ℕ) → (Fin k → Bool) → (ℤ × ℤ) → ℤ × ℤ
  | 0, _, state => state
  | k + 1, word, state =>
      applyTargetWord k (fun i => word i.succ)
        (if word 0 then targetDown state else targetUp state)

/-- No nontrivial fixed-length affine state dilation can intertwine both source
branches with target words of the same fixed length. -/
def FixedTimeAffineDilationObstruction : Prop :=
  ∀ (k : ℕ) (A B C D : ℤ),
    2 ≤ k → A ≠ 0 →
      ¬ ∃ (wordUp wordDown : Fin k → Bool),
        (∀ j g : ℤ,
          applyTargetWord k wordUp (affineStateMap k A B C D j g) =
            affineStateMap k A B C D (j + 1) (movingGapUp j g)) ∧
        (∀ j g : ℤ,
          applyTargetWord k wordDown (affineStateMap k A B C D j g) =
            affineStateMap k A B C D (j + 1) (movingGapDown j g))

end MathlibPlus.Open.ResearchFormalization.SignedGap
