import Mathlib

namespace MathlibPlus.Combinatorics

noncomputable section

/-- Positive internal lengths up to radius six, represented by 1,...,6. -/
def PositiveLength6 := {ℓ : Fin 7 // 0 < ℓ.1}

instance positiveLength6Finite : Finite PositiveLength6 :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance positiveLength6Fintype : Fintype PositiveLength6 :=
  Fintype.ofFinite _

/-- The exact radius-six boundary carrier: seven binary pendant bits and four
positive internal lengths, with at least one length equal to six. -/
def RadiusSixBoundary5507 :=
  {ε : (Fin 7 → Bool) × (Fin 4 → PositiveLength6) //
    ∃ i : Fin 4, (ε.2 i).1 = 6}

instance radiusSixBoundaryFinite : Finite RadiusSixBoundary5507 :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance radiusSixBoundaryFintype : Fintype RadiusSixBoundary5507 :=
  Fintype.ofFinite _

/-- The grade used by the four internal lengths and the seven binary bits. -/
def grade5507 (lengths : Fin 4 → PositiveLength6) : ℕ :=
  2 * 7 + ∑ i : Fin 4, (lengths i).1.1

/-- Claim 5507: the exact finite grade ceiling and the exact radius-six
boundary-representative cardinality on the source carrier. -/
def gradeCeilingAndBoundaryRepresentativeCount_claim5507 : Prop :=
  (∀ lengths : Fin 4 → PositiveLength6,
    (∀ i : Fin 4, (lengths i).1 ≤ 5) →
      grade5507 lengths ≤ 34) ∧
    Fintype.card RadiusSixBoundary5507 = 85888

end

end MathlibPlus.Combinatorics
