import Mathlib

namespace MathlibPlus.Combinatorics.Claim21275

/-- Exact left-hand meet-closure reconstruction from admitted claim 21275.
Only the nonemptiness and empty-total-intersection hypotheses on `𝒝` used by
this direction are assumed. -/
theorem factorReconstruction_left_claim21275
    {α : Type*} (𝒜 𝒝 : Set (Set α))
    (hB_nonempty : 𝒝.Nonempty) (hB_empty : ⋂₀ 𝒝 = ∅) :
    ∀ A ∈ 𝒜, A = ⋂ B ∈ 𝒝, A ∪ B := by
  intro A hA
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro B
    rw [Set.mem_iInter]
    intro hB
    exact Set.mem_union_left B hx
  · intro hx
    by_contra hxA
    have hex : ∃ B ∈ 𝒝, x ∉ B := by
      by_contra h
      push Not at h
      have hxall : x ∈ ⋂₀ 𝒝 := by
        rw [Set.mem_sInter]
        intro B hB
        exact h B hB
      rw [hB_empty] at hxall
      exact hxall
    obtain ⟨B, hB, hxB⟩ := hex
    have hxBfun : ∀ B, x ∈ ⋂ (_ : B ∈ 𝒝), A ∪ B :=
      Set.mem_iInter.mp hx
    have hxunion : x ∈ A ∪ B :=
      Set.mem_iInter.mp (hxBfun B) hB
    rcases hxunion with hxA' | hxB'
    · exact hxA hxA'
    · exact hxB hxB'

/-- Exact right-hand meet-closure reconstruction from admitted claim 21275.
Only the nonemptiness and empty-total-intersection hypotheses on `𝒜` used by
this direction are assumed. -/
theorem factorReconstruction_right_claim21275
    {α : Type*} (𝒜 𝒝 : Set (Set α))
    (hA_nonempty : 𝒜.Nonempty) (hA_empty : ⋂₀ 𝒜 = ∅) :
    ∀ B ∈ 𝒝, B = ⋂ A ∈ 𝒜, A ∪ B := by
  intro B hB
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro A
    rw [Set.mem_iInter]
    intro hA
    exact Set.mem_union_right A hx
  · intro hx
    by_contra hxB
    have hex : ∃ A ∈ 𝒜, x ∉ A := by
      by_contra h
      push Not at h
      have hxall : x ∈ ⋂₀ 𝒜 := by
        rw [Set.mem_sInter]
        intro A hA
        exact h A hA
      rw [hA_empty] at hxall
      exact hxall
    obtain ⟨A, hA, hxA⟩ := hex
    have hxAfun : ∀ A, x ∈ ⋂ (_ : A ∈ 𝒜), A ∪ B :=
      Set.mem_iInter.mp hx
    have hxunion : x ∈ A ∪ B :=
      Set.mem_iInter.mp (hxAfun A) hA
    rcases hxunion with hxA' | hxB'
    · exact hxA hxA'
    · exact hxB hxB'

end MathlibPlus.Combinatorics.Claim21275
