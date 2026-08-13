import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim9649

/-- Any statistic that factors through the idempotent multiset support is
constant on multisets with equal support. -/
theorem support_factorization_forces_invariance_claim9649
    {α β : Type*} [DecidableEq α]
    (D : Multiset α → β) (d : Set α → β)
    (hD : ∀ s : Multiset α, D s = d (↑s.toFinset : Set α))
    {s t : Multiset α}
    (h_support : (↑s.toFinset : Set α) = (↑t.toFinset : Set α)) :
    D s = D t := by
  rw [hD s, hD t, h_support]

/-- A statistic distinguishing a singleton from its duplicated singleton
cannot descend through idempotent support. -/
theorem multiplicity_sensitive_not_support_factor_claim9649
    {α β : Type*} [DecidableEq α]
    (a : α) (D : Multiset α → β)
    (hneq : D ({a} : Multiset α) ≠ D (({a} + {a}) : Multiset α)) :
    ¬ ∃ d : Set α → β,
        ∀ s : Multiset α, D s = d (↑s.toFinset : Set α) := by
  rintro ⟨d, hD⟩
  apply hneq
  apply support_factorization_forces_invariance_claim9649 D d hD
  ext x
  simp

end MathlibPlus.Combinatorics.Claim9649
