import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.D0090Claim5264

noncomputable section
open scoped BigOperators

/-- Positive ordered arm compositions of a fixed total.  The finite value
carrier makes the ordered-arm incidence matrix explicit. -/
abbrev PositiveComposition (arms total : ℕ) :=
  {a : Fin arms → Fin (total + 1) //
    (∀ i, 0 < (a i).val) ∧ ∑ i, (a i).val = total}

def raisesTo {arms total : ℕ}
    (β : PositiveComposition arms (total - 1))
    (α : PositiveComposition arms total) (i : Fin arms) : Prop :=
  ∀ j, (α.1 j).val = (β.1 j).val + if j = i then 1 else 0

/-- One bulk arm-up row or one unit-facet row evaluated at an ordered target. -/
def orderedFacetEntry {arms total : ℕ}
    (β : PositiveComposition arms (total - 1))
    (α : PositiveComposition arms total) (facet : Bool) : ℚ :=
  letI := Classical.propDecidable
  (Finset.univ : Finset (Fin arms)).sum (fun i =>
    if raisesTo β α i ∧ (facet = false ∨ (β.1 i).val = 1) then 1 else 0)

/-- The ordered-arm bulk-plus-unit-facet incidence matrix. -/
def orderedFacetMatrix (arms total : ℕ) :
    Matrix (PositiveComposition arms (total - 1) × Bool)
      (PositiveComposition arms total) ℚ :=
  fun row α => orderedFacetEntry row.1 α row.2

/-- The target corank of the ordered-arm facet-split incidence matrix. -/
noncomputable def orderedFacetDefect (arms total : ℕ) : ℕ :=
  letI : Fintype (PositiveComposition arms total) := Fintype.ofFinite _
  letI : Fintype (PositiveComposition arms (total - 1)) := Fintype.ofFinite _
  Fintype.card (PositiveComposition arms total) -
    Matrix.rank (orderedFacetMatrix arms total)

/-- Claim 5264: the first six ordered-arm facet defects for three, four, and
five arms are the displayed diagnostic rows. -/
def claim5264 : Prop :=
  orderedFacetDefect 3 4 = 2 ∧
    orderedFacetDefect 3 5 = 0 ∧
    orderedFacetDefect 3 6 = 1 ∧
    orderedFacetDefect 3 7 = 0 ∧
    orderedFacetDefect 3 8 = 1 ∧
    orderedFacetDefect 3 9 = 0 ∧
    orderedFacetDefect 4 5 = 3 ∧
    orderedFacetDefect 4 6 = 2 ∧
    orderedFacetDefect 4 7 = 3 ∧
    orderedFacetDefect 4 8 = 2 ∧
    orderedFacetDefect 4 9 = 3 ∧
    orderedFacetDefect 4 10 = 3 ∧
    orderedFacetDefect 5 6 = 4 ∧
    orderedFacetDefect 5 7 = 5 ∧
    orderedFacetDefect 5 8 = 6 ∧
    orderedFacetDefect 5 9 = 10 ∧
    orderedFacetDefect 5 10 = 11 ∧
    orderedFacetDefect 5 11 = 14

end
end MathlibPlus.Open.ResearchFormalization.D0090Claim5264
