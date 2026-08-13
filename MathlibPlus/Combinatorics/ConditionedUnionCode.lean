import Mathlib.Data.Set.Lattice

namespace MathlibPlus.Combinatorics

/-- The exact conditioned-union identity from claim 21125. -/
theorem conditionedUnionIntersection_claim21125
    {α J : Type*} (Y : J → Set (Set α)) (G : Set α) (j : J)
    (hY : (Y j).Nonempty) :
    G ∪ ⋂₀ Y j = ⋂ H ∈ Y j, G ∪ H := by
  ext x
  constructor
  · intro hx
    rcases hx with hxG | hxI
    · exact Set.mem_iInter₂.mpr fun H hH => Or.inl hxG
    · exact Set.mem_iInter₂.mpr fun H hH => Or.inr (Set.mem_sInter.mp hxI H hH)
  · intro hx
    by_cases hxG : x ∈ G
    · exact Or.inl hxG
    · right
      apply Set.mem_sInter.mpr
      intro H hH
      have hxH : x ∈ G ∪ H := Set.mem_iInter₂.mp hx H hH
      exact hxH.resolve_left hxG

end MathlibPlus.Combinatorics
