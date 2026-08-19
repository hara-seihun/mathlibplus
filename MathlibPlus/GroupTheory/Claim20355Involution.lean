import Mathlib

namespace MathlibPlus.GroupTheory.Claim20355

/-- Claim 20355: an involution whose permutation support has at least ten
points consists of at least five transposition cycles. -/
def involution_has_five_transpositions : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α),
    σ ^ 2 = 1 →
    σ ≠ 1 →
    10 ≤ σ.support.card →
      5 ≤ σ.cycleType.card ∧
        ∀ n ∈ σ.cycleType, n = 2

end MathlibPlus.GroupTheory.Claim20355
