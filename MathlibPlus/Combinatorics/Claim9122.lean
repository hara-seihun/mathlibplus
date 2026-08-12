import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim9122

/-- A permutation has the exact card-involution shape from claim 9122: it
fixes the deleted vertex, swaps two disjoint pairs of remaining vertices, and
fixes every other vertex. -/
def exactlyTwoTranspositionCardInvolution
    {α : Type*} [DecidableEq α]
    (deleted : α) (σ : Equiv.Perm α) : Prop :=
  Function.Involutive σ ∧
    ∃ a b c d : α,
      deleted ≠ a ∧ deleted ≠ b ∧ deleted ≠ c ∧ deleted ≠ d ∧
      a ≠ b ∧ c ≠ d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      σ deleted = deleted ∧
      σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c ∧
      ∀ x : α,
        x ≠ a → x ≠ b → x ≠ c → x ≠ d → σ x = x

end MathlibPlus.Combinatorics.Claim9122
