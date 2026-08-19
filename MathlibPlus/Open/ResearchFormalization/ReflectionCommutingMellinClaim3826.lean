import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ReflectionCommutingMellinClaim3826

/-- The reflection-commuting Mellin quotient identity, wherever both reflected
Mellin denominators are nonzero. -/
def reflectionCommutingMellinQuotient_claim3826 : Prop :=
  ∀ (M_p M_q : ℂ → ℂ) (s : ℂ),
    M_p s * M_q (1 - s) = M_q s * M_p (1 - s) →
      M_q s ≠ 0 →
        M_q (1 - s) ≠ 0 →
          M_p (1 - s) / M_q (1 - s) = M_p s / M_q s

end MathlibPlus.Open.ResearchFormalization.ReflectionCommutingMellinClaim3826
