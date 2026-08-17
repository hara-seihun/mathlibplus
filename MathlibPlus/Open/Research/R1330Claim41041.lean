import MathlibPlus.Open.Research.R1330Claim41040

namespace MathlibPlus.Open.Research.R1330Formalization_41041

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41040

/-- A literal intersection of two subgroups is trivial when their meet is the
bottom subgroup.  This is the selected-line condition in Claim 41041. -/
def literalIntersectionTrivial {G : Type*} [Group G]
    (D E : Subgroup G) : Prop :=
  D ⊓ E = ⊥

/-- Claim 41041.  The two selected characteristic prime lines may have trivial
literal intersection, while every source/target order-p line pair is conjugate
inside the actual generated group and the two regular copies are conjugate
there as well. -/
def claim41041 : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p),
      (∀ z : Ω p, F z = blockShear p z) ∧
      blockKernel p F F ∧
      characteristicTranslationKernel p ∧
      characteristicTranslatedKernel p F ∧
      ∃ D E : Subgroup (Equiv.Perm (Ω p)),
        orderPSubgroup p (translationKernel p) D ∧
        orderPSubgroup p (translatedKernel p F) E ∧
        literalIntersectionTrivial D E ∧
        allPrimeLineConjugacy p F ∧
        fullCopiesConjugate p F

end

end MathlibPlus.Open.Research.R1330Formalization_41041
