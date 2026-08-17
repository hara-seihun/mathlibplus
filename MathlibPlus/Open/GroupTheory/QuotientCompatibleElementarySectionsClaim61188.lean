import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- The elementary abelian group of rank `r` over the prime field of order `p`. -/
abbrev elementaryAbelianGroupOfRank (p r : ℕ) :=
  Multiplicative (Fin r → ZMod p)

/-- An abstract subgroup has the indicated elementary abelian `p`-rank. -/
def hasElementaryAbelianRank {E : Type*} [Group E]
    (H : Subgroup E) (p r : ℕ) : Prop :=
  Nonempty (H ≃* elementaryAbelianGroupOfRank p r)

/--
Claim 61188.  Finite elementary abelian subgroups of equal rank whose images
coincide in a normal quotient admit a pointwise quotient-compatible group
isomorphism.  The assertion is only about the subgroup correspondence and its
quotient compatibility; it includes no ambient relation or Cayley-set claim.
-/
def quotientCompatibleElementarySections_claim61188 : Prop :=
  ∀ (E : Type*) [Group E]
    (A : Subgroup E) [A.Normal]
    (p r : ℕ), Nat.Prime p →
    ∀ (P Q : Subgroup E),
      Finite P →
      Finite Q →
      hasElementaryAbelianRank P p r →
      hasElementaryAbelianRank Q p r →
      Subgroup.map (QuotientGroup.mk' A) P =
        Subgroup.map (QuotientGroup.mk' A) Q →
      ∃ beta : P ≃* Q,
        ∀ x : P,
          QuotientGroup.mk' A ((beta x : Q) : E) =
            QuotientGroup.mk' A (x : E)

end MathlibPlus.Open.GroupTheory
