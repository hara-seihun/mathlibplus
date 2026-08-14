import Mathlib

namespace MathlibPlus.GroupTheory

/-- The additive subgroup carrier in claim 41198 has only the two possibilities
`0` and `𝔽₅`; this is the finite-field component of the source claim. -/
theorem addSubgroup_zmod_five_eq_bot_or_top_claim41198
    (H : AddSubgroup (ZMod 5)) : H = ⊥ ∨ H = ⊤ := by
  letI : Fact (Nat.Prime (Nat.card (ZMod 5))) := ⟨by
    simpa only [Nat.card_zmod] using (show Nat.Prime 5 by norm_num)⟩
  exact AddSubgroup.eq_bot_or_eq_top_of_prime_card H

end MathlibPlus.GroupTheory
