import Mathlib

namespace MathlibPlus.Algebra.Claim32121

/-- The period set of a multiplier on an additive group is an additive
subgroup, and every period has the base value. -/
theorem multiplierPeriodSubgroup
    {H α : Type*} [AddGroup H] (mult : H → α) :
    let P : AddSubgroup H :=
      { carrier := {h | ∀ k : H, mult (h + k) = mult k}
        zero_mem' := by
          intro k
          simp
        add_mem' := by
          intro a b ha hb k
          calc
            mult ((a + b) + k) = mult (a + (b + k)) := by rw [add_assoc]
            _ = mult (b + k) := ha (b + k)
            _ = mult k := hb k
        neg_mem' := by
          intro a ha k
          have h := ha (-a + k)
          simpa only [add_neg_cancel_left] using h.symm }
    (∀ h : H, h ∈ P ↔ ∀ k : H, mult (h + k) = mult k) ∧
      (∀ h : H, h ∈ P → mult h = mult 0) := by
  dsimp
  constructor
  · intro h
    rfl
  · intro h hh
    simpa using hh 0

end MathlibPlus.Algebra.Claim32121
