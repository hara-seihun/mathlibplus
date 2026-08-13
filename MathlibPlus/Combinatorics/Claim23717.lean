import Mathlib

namespace MathlibPlus.Combinatorics.Claim23717

/-- A nonempty finite prediction contained in the true singleton support is that singleton. -/
theorem prediction_eq_owner {α : Type*} [DecidableEq α] (r : α) (prediction trueSupport : Finset α)
    (hprivate : trueSupport = {r}) (hnonempty : prediction.Nonempty)
    (hcontained : prediction ⊆ trueSupport) :
    prediction = {r} := by
  subst trueSupport
  rcases hnonempty with ⟨x, hx⟩
  have hxr : x = r := by
    simpa using hcontained hx
  ext y
  constructor
  · intro hy
    have hyr : y = r := by
      simpa using hcontained hy
    simpa [hyr]
  · intro hy
    have hr : r ∈ prediction := by simpa [hxr] using hx
    have hyr : y = r := by simpa using hy
    simpa [hyr] using hr

end MathlibPlus.Combinatorics.Claim23717
