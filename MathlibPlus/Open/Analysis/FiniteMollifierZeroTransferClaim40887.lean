import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 40887: under the displayed quotient representation with a nonzero
B, a finite mollifier cannot cancel a zero of H; no nonvanishing condition on
M is added. -/
def finiteMollifierZeroTransfer_claim40887 : Prop :=
  ∀ {Z S : Type*} (s : Z → S)
    (B G H : Z → ℂ) (M : S → ℂ),
    (∀ z : Z, B z ≠ 0) →
      (∀ z : Z, G z = M (s z) * H z / B z) →
        (∀ z : Z, H z = 0 → G z = 0) ∧
          ((∀ z : Z, G z ≠ 0) → ∀ z : Z, H z ≠ 0)

end MathlibPlus.Open.Analysis
