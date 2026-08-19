import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2037SupportSemilatticeClaim35483

open scoped BigOperators

noncomputable section

abbrev MemberFamily (α : Type*) := Finset (Finset α)
abbrev SupportAtom (α : Type*) := Finset α × Finset (Finset α)

def uniformDistinctFamily {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (r : ℕ) : Prop :=
  F.Nonempty ∧ ∀ A ∈ F, A.card = r

def memberSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (T : Finset α) : Finset (Finset α) :=
  F.filter (fun A => T ⊆ A)

def complementMemberSupport {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (T : Finset α) : Finset (Finset α) :=
  F \ memberSupport F T

def groundSubsets {α : Type*} [Fintype α] [DecidableEq α] : Finset (Finset α) :=
  Finset.univ

def nonemptyGroundSubsets {α : Type*} [Fintype α] [DecidableEq α] :
    Finset (Finset α) :=
  groundSubsets.filter (fun T => T.Nonempty)

def supportAtom {α : Type*} [DecidableEq α]
    (F : MemberFamily α) (T : Finset α) : SupportAtom α :=
  (T, memberSupport F T)

def supportMeet {α : Type*} [DecidableEq α]
    (x y : SupportAtom α) : SupportAtom α :=
  (x.1 ∪ y.1, x.2 ∩ y.2)

def allOrderSupportValues {α : Type*} [Fintype α] [DecidableEq α]
    (F : MemberFamily α) : Finset (Finset (Finset α)) :=
  insert ∅ (nonemptyGroundSubsets.image (memberSupport F))

def supportIntersectionSemilattice {α : Type*} [Fintype α] [DecidableEq α]
    (F : MemberFamily α) : Prop :=
  ∀ S ∈ allOrderSupportValues F, ∀ R ∈ allOrderSupportValues F,
    S ∩ R ∈ allOrderSupportValues F

def fixedShadowSupportLayer {α : Type*} [Fintype α] [DecidableEq α]
    (F : MemberFamily α) (q : ℕ) : Finset (SupportAtom α) :=
  (groundSubsets.filter (fun T => T.card = q)).image (supportAtom F)

def fixedShadowLayerNonintersection {α : Type*} [Fintype α] [DecidableEq α]
    (F : MemberFamily α) : Prop :=
  ∀ q : ℕ, ∀ T U : Finset α,
    supportAtom F T ∈ fixedShadowSupportLayer F q →
    supportAtom F U ∈ fixedShadowSupportLayer F q →
    (T ∪ U).card > q →
    supportMeet (supportAtom F T) (supportAtom F U) ∉
      fixedShadowSupportLayer F q

/-- The exact all-order member-support identities, bottom support, and
fixed-shadow coordinate boundary from Claim 35483. -/
def claim35483_allOrderLinkSupportSemilattice : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (F : MemberFamily α) (r : ℕ),
    uniformDistinctFamily F r →
      (∀ T U : Finset α,
        T.Nonempty → U.Nonempty →
          memberSupport F T ∩ memberSupport F U =
              memberSupport F (T ∪ U) ∧
            complementMemberSupport F T ∪ complementMemberSupport F U =
              complementMemberSupport F (T ∪ U)) ∧
      (∅ : Finset (Finset α)) ∈ allOrderSupportValues F ∧
      supportIntersectionSemilattice F ∧
      (∀ q : ℕ, ∀ T U : Finset α,
        supportAtom F T ∈ fixedShadowSupportLayer F q →
        supportAtom F U ∈ fixedShadowSupportLayer F q →
        (T ∪ U).card > q →
        supportMeet (supportAtom F T) (supportAtom F U) =
          (T ∪ U, memberSupport F (T ∪ U)) ∧
        supportMeet (supportAtom F T) (supportAtom F U) ∉
          fixedShadowSupportLayer F q)

end

end MathlibPlus.Open.ResearchFormalization.R2037SupportSemilatticeClaim35483
