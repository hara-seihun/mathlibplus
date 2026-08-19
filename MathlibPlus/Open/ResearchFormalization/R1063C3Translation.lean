import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1063C3Translation

noncomputable section

open scoped Pointwise

/-- Claim 29952: every proper nonempty subset of the concrete cyclic group
`C₃ = ZMod 3` has trivial translation stabilizer; the empty and full subsets
are invariant under all translations. -/
def properNonemptyC3SubsetsHaveTrivialTranslationStabilizer_claim29952 : Prop :=
  (∀ (S : Set (ZMod 3)),
    S.Nonempty → S ≠ (Set.univ : Set (ZMod 3)) →
      ∀ t : ZMod 3,
        Set.image (fun x : ZMod 3 => x + t) S = S → t = 0) ∧
    (∀ t : ZMod 3,
      Set.image (fun x : ZMod 3 => x + t) (∅ : Set (ZMod 3)) = ∅ ∧
        Set.image (fun x : ZMod 3 => x + t) (Set.univ : Set (ZMod 3)) =
          Set.univ)

end

end MathlibPlus.Open.ResearchFormalization.R1063C3Translation
