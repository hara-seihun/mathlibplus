import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- A local card equation changes a component-count signature by the indicated unit transfer. -/
theorem unitTransferSignature
    {α : Type*} [DecidableEq α]
    (source target : α → ℤ) (removed added : α)
    (h : ∀ c : α,
      source c - (if c = removed then 1 else 0) =
        target c - (if c = added then 1 else 0)) :
    ∀ c : α,
      target c - source c =
        (if c = added then 1 else 0) - (if c = removed then 1 else 0) := by
  intro c
  specialize h c
  by_cases hremoved : c = removed <;>
    by_cases hadded : c = added <;>
      simp [hremoved, hadded] at h ⊢ <;>
      linarith

end MathlibPlus.Combinatorics
