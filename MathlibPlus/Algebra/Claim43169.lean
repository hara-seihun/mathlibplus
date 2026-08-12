import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

namespace MathlibPlus.Algebra.Claim43169

/-!
Formalization of admitted claim 43169 (locator `R-2206`).  The group is
represented by the exact product of two multiplicative copies of `ZMod 3` and
`DihedralGroup 5`; the second conjunct records the nonidentity cardinality.
-/

/-- `Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × D₁₀` has order 90,
and its nonidentity elements have cardinality 89. -/
theorem groupCard_and_nonidentityCard :
    let G := Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × DihedralGroup 5
    Fintype.card G = 90 ∧ Fintype.card {g : G // g ≠ 1} = 89 := by
  dsimp
  constructor
  · simp [DihedralGroup.card]
  · rw [Fintype.card_subtype_compl (p := fun g :
        Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × DihedralGroup 5 => g = 1)]
    simp [DihedralGroup.card]

end MathlibPlus.Algebra.Claim43169
