import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim19615

/-!
Formalization of admitted claim 19615.  The pairing is stated on arbitrary
basis labels with an explicit decidable equality and finite automorphism types.
The source's ambient updown category and its adjointness axiom are not silently
reconstructed here.
-/

/-- The automorphism-weighted basis pairing is positive diagonal. -/
theorem automorphismWeightedBasisPairing_positiveDiagonal
    (P : Type*) [DecidableEq P]
    (Aut : P → Type*) [∀ p, Fintype (Aut p)]
    (hAut : ∀ p : P, Nonempty (Aut p)) :
    let pairing : P → P → ℚ := fun p p' =>
      if p = p' then (Fintype.card (Aut p) : ℚ) else 0
    (∀ p : P, 0 < pairing p p) ∧
      (∀ p p' : P, p ≠ p' → pairing p p' = 0) := by
  dsimp
  constructor
  · intro p
    simp only [if_pos rfl]
    exact_mod_cast (Fintype.card_pos_iff.mpr (hAut p))
  · intro p p' hne
    simp [hne]

end MathlibPlus.Algebra.Claim19615
