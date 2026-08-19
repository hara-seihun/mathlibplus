import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 30057: every nonempty proper subset of the cyclic group of order
seven has seven distinct additive translates. -/
def primeOrderTranslationsDistinct_30057 : Prop :=
  ∀ B : Finset (ZMod 7),
    B.Nonempty → B ⊂ (Finset.univ : Finset (ZMod 7)) →
      let translate : Finset (ZMod 7) → ZMod 7 → Finset (ZMod 7) :=
        fun S t => S.image (fun x => x + t)
      Fintype.card {C : Finset (ZMod 7) // ∃ t : ZMod 7, translate B t = C} = 7

end MathlibPlus.Combinatorics
