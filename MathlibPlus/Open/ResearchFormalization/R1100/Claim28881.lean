import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationR1100

/-- Claim 28881: `F` has a nonzero translation period. -/
def nonzeroTranslationPeriod_claim28881
    (F : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3)) : Prop :=
  ∃ s : Fin 2 → ZMod 3, s ≠ 0 ∧ ∀ x, F (x + s) = F x

end MathlibPlus.Open.ResearchFormalizationR1100
