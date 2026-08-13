import Mathlib.Data.Set.Lattice

namespace MathlibPlus.Combinatorics

/-- Equality after adjoining a common set is exactly equality of the traces
outside that common set. -/
theorem union_eq_union_iff_diff_eq_diff_claim42269 {α : Type*}
    (A A' J : Set α) :
    A ∪ J = A' ∪ J ↔ A \ J = A' \ J := by
  constructor
  · intro h
    ext x
    by_cases hx : x ∈ J
    · simp [hx]
    · simpa [hx] using Set.ext_iff.mp h x
  · intro h
    ext x
    by_cases hx : x ∈ J
    · simp [hx]
    · have hx' := Set.ext_iff.mp h x
      simpa [hx] using hx'

end MathlibPlus.Combinatorics
