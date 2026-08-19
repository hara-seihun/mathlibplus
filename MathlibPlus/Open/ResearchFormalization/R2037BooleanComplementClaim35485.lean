import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2037BooleanComplementClaim35485

open scoped BigOperators

noncomputable section

abbrev MemberFamily (α : Type*) := Finset (Finset α)

def uniformDistinctFamily {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (r : ℕ) : Prop :=
  F.Nonempty ∧ ∀ A ∈ F, A.card = r

def sourceSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (T : Finset α) : Finset (Finset α) :=
  F.filter (fun A => T ⊆ A)

def sourceComplementSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (T : Finset α) : Finset (Finset α) :=
  F \ sourceSupport F T

def nonemptyBooleanDomain {α : Type*} [DecidableEq α]
    (F : MemberFamily α) : Finset (Finset α) :=
  F.biUnion (fun A => A.powerset.erase ∅)

def derivedMember {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (A : Finset α) : Finset (Option (Finset α)) :=
  ({none} : Finset (Option (Finset α))) ∪
    ((nonemptyBooleanDomain F).filter (fun T => ¬ T ⊆ A)).image
      (fun T : Finset α => some T)

def derivedFamily {α : Type*} [DecidableEq α]
    (F : MemberFamily α) : Finset (Finset (Option (Finset α))) :=
  F.image (derivedMember F)

def derivedRank {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (r : ℕ) : ℕ :=
  (nonemptyBooleanDomain F).card + 2 - 2 ^ r

def derivedUniformRank {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (r : ℕ) : Prop :=
  ∀ A ∈ F, (derivedMember F A).card = derivedRank F r

def derivedCoordinateSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (T : Finset α) : Finset (Finset α) :=
  F.filter (fun A => ¬ T ⊆ A)

def derivedStarSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) : Finset (Finset α) :=
  F

def derivedSupportLaw {α : Type*} [DecidableEq α]
    (F : MemberFamily α) : Prop :=
  (∀ T : Finset α, T ∈ nonemptyBooleanDomain F →
    derivedCoordinateSupport F T = sourceComplementSupport F T) ∧
  derivedStarSupport F = F

def derivedSupportUnionClosure {α : Type*} [DecidableEq α]
    (F : MemberFamily α) : Prop :=
  ∀ T U : Finset α,
    T ∈ nonemptyBooleanDomain F → U ∈ nonemptyBooleanDomain F →
      derivedCoordinateSupport F T ∪ derivedCoordinateSupport F U =
        if T ∪ U ∈ nonemptyBooleanDomain F then
          derivedCoordinateSupport F (T ∪ U)
        else derivedStarSupport F

def unrealizedUnionHasEmptySourceSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) : Prop :=
  ∀ T U : Finset α,
    T ∈ nonemptyBooleanDomain F → U ∈ nonemptyBooleanDomain F →
    T ∪ U ∉ nonemptyBooleanDomain F →
    sourceSupport F (T ∪ U) = ∅

/-- The exact down-set complement construction, its non-wrapped Nat rank,
indexed complement supports, star completion, and realized-coordinate union
closure from Claim 35485. -/
def claim35485_fullBooleanComplementConstruction : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (r : ℕ),
    uniformDistinctFamily F r →
      derivedUniformRank F r ∧
      (∀ A ∈ F,
        derivedMember F A ∈ derivedFamily F) ∧
      derivedSupportLaw F ∧
      unrealizedUnionHasEmptySourceSupport F ∧
      derivedSupportUnionClosure F

end

end MathlibPlus.Open.ResearchFormalization.R2037BooleanComplementClaim35485
