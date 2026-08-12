import Mathlib

namespace MathlibPlus.Combinatorics.Claim9646

/-- Native set-valued scars are idempotent under the source union operation. -/
theorem scar_union_idempotent {α : Type*} (A : Set α) :
    A ∪ A = A := by
  ext x
  simp

end MathlibPlus.Combinatorics.Claim9646
