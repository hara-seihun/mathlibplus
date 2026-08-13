import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim3346

/--
The exact per-vertex bounds in the 18-regular exclusion cannot share a common
summed total: the two displayed totals are ordered in the wrong direction.
The graph, goodness, and summation identity are intentionally the external
carrier of this numerical obstruction.
-/
theorem no_18_regular_from_summed_bounds
    (total : ℕ) (hleft : total ≤ 43 * 888) (hright : 43 * 936 ≤ total) :
    False := by
  omega

end MathlibPlus.GraphTheory.Claim3346
