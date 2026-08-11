import Mathlib

namespace MathlibPlus.Algebra.Claim20863

/-- The collapse/pure-collision/activation trichotomy, with the source's
membership facts for `D` and `E` made explicit rather than hidden in names.
Here `J` is the type of join-irreducible labels, `j` is the distinguished
label, and `E s` is the set of active labels attached to `s`. -/
theorem statusTrichotomy_claim20863
    {α J : Type*} (D : Set α) (E : α → Set J) (j : J)
    (hEmpty : ∀ s : α, s ∉ D → E s = ∅)
    (hDistinguished : ∀ s : α, s ∈ D → j ∈ E s)
    (s : α) :
    (s ∉ D ∧ E s = ∅) ∨
      (s ∈ D ∧ E s = {j}) ∨
      (s ∈ D ∧ ∃ k : J, k ∈ E s ∧ k ≠ j) := by
  classical
  by_cases hs : s ∈ D
  · have hj : j ∈ E s := hDistinguished s hs
    by_cases hsingleton : E s = {j}
    · exact Or.inr (Or.inl ⟨hs, hsingleton⟩)
    · right
      right
      have hother : ∃ k : J, k ∈ E s ∧ k ≠ j := by
        by_contra hnone
        apply hsingleton
        ext k
        constructor
        · intro hk
          have hk_eq : k = j := by
            by_contra hne
            exact hnone ⟨k, hk, hne⟩
          simpa [hk_eq]
        · intro hk
          have hk_eq : k = j := by simpa using hk
          simpa [hk_eq] using hj
      exact ⟨hs, hother⟩
  · exact Or.inl ⟨hs, hEmpty s hs⟩

end MathlibPlus.Algebra.Claim20863
