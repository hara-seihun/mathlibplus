import Mathlib

namespace MathlibPlus.Combinatorics.Claim28491

/-- A family of 30 inverse atoms has exactly 2^30 selectable subfamilies;
the source identification of inverse-closed connection sets with these atoms is
left explicit for fidelity review. -/
theorem inverse_atom_choice_count_claim28491
    {α : Type*} [DecidableEq α] (atoms : Finset α)
    (hcard : atoms.card = 30) :
    (atoms.powerset).card = 1073741824 := by
  rw [Finset.card_powerset, hcard]
  norm_num

end MathlibPlus.Combinatorics.Claim28491
