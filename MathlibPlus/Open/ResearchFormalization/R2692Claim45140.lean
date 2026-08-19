import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2692Claim45140

noncomputable section

abbrev Family (X : Type*) := Finset (Finset X)

def unionClosed {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ ⦃A B : Finset X⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def familySupport {X : Type*} [DecidableEq X]
    (F : Family X) : Finset X :=
  F.biUnion id

def familyFrequency {X : Type*} [DecidableEq X]
    (F : Family X) (x : X) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

/-- Inclusion-minimal among the nonempty members of `F`. -/
def minimalNonemptyMembers {X : Type*} [DecidableEq X]
    (F : Family X) : Finset (Finset X) :=
  F.filter (fun A =>
    A.Nonempty ∧
      ∀ B : Finset X, B ∈ F → B.Nonempty → B ⊆ A → B = A)

def franklNegation {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ x ∈ familySupport F,
    2 * familyFrequency F x < F.card

def principalFilter {X : Type*} [DecidableEq X]
    (F : Family X) (M : Finset X) : Finset (Finset X) :=
  F.filter (fun A => M ⊆ A)

def pairwiseDisjointMinima {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ A ∈ minimalNonemptyMembers F,
    ∀ B ∈ minimalNonemptyMembers F,
      A ≠ B → Disjoint A B

def someHalfSizedWholeMinimumFilter {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∃ M ∈ minimalNonemptyMembers F,
    2 * (principalFilter F M).card ≥ F.card

/-- Claim R-2692.3: Frankl negation and at most three inclusion-minimal
nonempty members force exactly three pairwise-disjoint minima.  The separate
non-implication records that the corresponding disjointness hypothesis alone
does not force a half-sized whole-minimum principal filter. -/
def claim45140 : Prop :=
  (∀ {X : Type*} [DecidableEq X]
      (F : Family X),
      (∃ A ∈ F, A.Nonempty) →
      unionClosed F →
      franklNegation F →
      (minimalNonemptyMembers F).card ≤ 3 →
      (minimalNonemptyMembers F).card = 3 ∧
        pairwiseDisjointMinima F) ∧
    (¬ ∀ {X : Type*} [DecidableEq X]
      (F : Family X),
      unionClosed F ∧
        (minimalNonemptyMembers F).card = 3 ∧
        pairwiseDisjointMinima F →
        someHalfSizedWholeMinimumFilter F)

end

end MathlibPlus.Open.ResearchFormalization.R2692Claim45140
