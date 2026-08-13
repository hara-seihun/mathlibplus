import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim9648

/-- No translation from set union to multiset addition can send every
singleton to the corresponding singleton multiset. -/
theorem singleton_set_to_multiset_union_impossible
    {α : Type*} [Nonempty α]
    (T : Set α → Multiset α)
    (hsingleton : ∀ a, T ({a} : Set α) = {a})
    (hunion : ∀ s t, T (s ∪ t) = T s + T t) : False := by
  classical
  let a : α := Classical.choice ‹Nonempty α›
  have h := hunion ({a} : Set α) ({a} : Set α)
  rw [Set.union_self, hsingleton] at h
  have hcount := congrArg (Multiset.count a) h
  simp at hcount

end MathlibPlus.Algebra.Claim9648
