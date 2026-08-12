import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum

namespace MathlibPlus.GroupTheory.Claim31005

/-- Every finite permutation of odd order has positive sign. -/
theorem odd_order_perm_is_even
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (hodd : Odd (orderOf σ)) :
    Equiv.Perm.sign σ = 1 := by
  have hsign : (Equiv.Perm.sign σ) ^ orderOf σ = 1 := by
    rw [← Equiv.Perm.sign.map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact h
  · exfalso
    rw [h, Odd.neg_one_pow hodd] at hsign
    have hval := congrArg (fun u : ℤˣ => (u : ℤ)) hsign
    norm_num at hval

end MathlibPlus.GroupTheory.Claim31005
