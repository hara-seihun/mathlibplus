import Mathlib

namespace MathlibPlus.Combinatorics.Claim48694

/-- A coordinate occurring in every member of a finite union-closed family has
full frequency, and therefore occurs in at least half of the family. -/
theorem universal_coordinate_frequency
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (_hUnion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (_hground : (F.biUnion id).Nonempty)
    (x : α)
    (_hxground : x ∈ F.biUnion id)
    (hx : ∀ A ∈ F, x ∈ A) :
    (F.filter (fun A => x ∈ A)).card = F.card ∧
      F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card := by
  have hfilter : F.filter (fun A => x ∈ A) = F := by
    apply Finset.filter_eq_self.mpr
    intro A hA
    exact hx A hA
  rw [hfilter]
  constructor
  · rfl
  · omega

end MathlibPlus.Combinatorics.Claim48694
