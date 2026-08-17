import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1539Claim37761

noncomputable section

abbrev A4 := alternatingGroup (Fin 4)
abbrev LiftedPoint := ZMod 5 × ZMod 5 × A4

/-- The common-`C₅` lift has two translation coordinates and left/right
`A₄` multiplication on the third coordinate.  Its generated-image action is
therefore parametrized by the four displayed factors. -/
def liftedGeneratedImageAction (d c : ZMod 5) (l r : A4)
    (x : LiftedPoint) : LiftedPoint :=
  (x.1 + d, x.2.1 + c, l * x.2.2 * r)

/-- Inversion of only the `A₄` coordinate in the degree-300 lift. -/
def a4OnlyInversion (x : LiftedPoint) : LiftedPoint :=
  (x.1, x.2.1, x.2.2⁻¹)

/-- The carrier of unordered pairs of distinct points, represented by
two-element finite subsets. -/
def unorderedPairs : Finset (Finset LiftedPoint) := by
  classical
  exact (Finset.univ : Finset (Finset LiftedPoint)).filter
    (fun p => p.card = 2)

/-- Equality of orbital colors for the lifted generated image. -/
def sameLiftedOrbital (p q : Finset LiftedPoint) : Prop :=
  ∃ (d c : ZMod 5) (l r : A4),
    p.image (liftedGeneratedImageAction d c l r) = q

/-- Unordered pairs whose color changes under `A₄`-only inversion. -/
def movedByA4OnlyInversion : Finset (Finset LiftedPoint) := by
  classical
  exact unorderedPairs.filter
    (fun p => ¬ sameLiftedOrbital p (p.image a4OnlyInversion))

/-- Claim 37761: the `A₄`-only inversion moves exactly 28,800 of the
44,850 unordered degree-300 pairs between orbital colors.  No orbital-size
profile is added to the admitted target. -/
def claim37761_liftedA4OnlyInversionMoves : Prop :=
  movedByA4OnlyInversion.card = 28800 ∧
    unorderedPairs.card = 44850

end

end MathlibPlus.Open.ResearchFormalization.R1539Claim37761
