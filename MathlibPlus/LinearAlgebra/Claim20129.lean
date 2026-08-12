import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim20129

/-- The displayed loop-column obstruction from claim 20129, with the
packet's otherwise unspecified observable `r` represented abstractly. -/
theorem loopColumnCannotBeRepaired_claim20129 {α : Type*} [DecidableEq α]
    (e : α) (r : Finset α → ℕ) (hr : r {e} = 0) :
    ∀ k : ℕ, ¬ (({e} : Finset α).card ≤ k * r {e}) := by
  intro k h
  simp [hr] at h

end MathlibPlus.LinearAlgebra.Claim20129
