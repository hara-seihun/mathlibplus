import Mathlib

namespace MathlibPlus.Combinatorics.Claim19959

/-! The support of a ground coordinate is the set of member indices containing it. -/

/-- Distinct members have a nonempty incidence support that separates every pair. -/
theorem distinct_members_have_separating_supports
    {α : Type*} {m : ℕ} (A : Fin m → Set α)
    (hDistinct : Pairwise (fun i j => A i ≠ A j)) :
    let support : α → Set (Fin m) := fun x => {i | x ∈ A i}
    ∀ i j : Fin m, i ≠ j →
      ∃ x : α, (support x).Nonempty ∧
        ((i ∈ support x ∧ j ∉ support x) ∨
          (j ∈ support x ∧ i ∉ support x)) := by
  dsimp
  intro i j hij
  have hne : A i ≠ A j := hDistinct hij
  by_contra hno
  apply hne
  apply Set.ext
  intro x
  by_cases hxi : x ∈ A i
  · have hxj : x ∈ A j := by
      by_contra hxj
      apply hno
      exact ⟨x, ⟨i, hxi⟩, Or.inl ⟨hxi, hxj⟩⟩
    simp [hxi, hxj]
  · have hxj : x ∉ A j := by
      by_contra hxj
      apply hno
      exact ⟨x, ⟨j, hxj⟩, Or.inr ⟨hxj, hxi⟩⟩
    simp [hxi, hxj]

end MathlibPlus.Combinatorics.Claim19959
