import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 42342: strict abundance of a coordinate among the nonempty members
of a finite family remains abundance after adjoining the empty member. -/
theorem strictNonemptyAbundanceLift_claim42342
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) (hEmpty : ∅ ∈ F) :
    let F₀ := F.erase ∅
    let f := (F₀.filter (fun A => x ∈ A)).card
    (2 * f > F₀.card) →
      2 * (F.filter (fun A => x ∈ A)).card ≥ F.card := by
  dsimp
  have hcard : (F.erase ∅).card = F.card - 1 := by
    exact Finset.card_erase_of_mem hEmpty
  have hcount :
      ((F.erase ∅).filter (fun A => x ∈ A)).card =
        (F.filter (fun A => x ∈ A)).card := by
    rw [Finset.filter_erase]
    simp
  omega

end MathlibPlus.Combinatorics
