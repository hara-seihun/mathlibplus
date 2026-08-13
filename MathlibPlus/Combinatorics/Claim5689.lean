import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim5689

/-- The balanced flow on a colored star has the same incidence divergence as
its pairwise star: every nonpivot value is its edge flow, and the pivot value
is the negative sum of the nonpivot flows. -/
theorem star_divergence_matches_balanced_flow
    {C T R : Type*} [Fintype C] [DecidableEq C]
    [AddCommGroup R]
    (c₀ : C) (w : T → C → R)
    (hbal : ∀ t, w t c₀ = -∑ c ∈ (Finset.univ.erase c₀), w t c) :
    ∀ t c,
      (if c = c₀ then -∑ c' ∈ (Finset.univ.erase c₀), w t c' else w t c) =
        w t c := by
  intro t c
  by_cases hc : c = c₀
  · simpa [hc] using (hbal t).symm
  · simp [hc]

end MathlibPlus.Combinatorics.Claim5689
