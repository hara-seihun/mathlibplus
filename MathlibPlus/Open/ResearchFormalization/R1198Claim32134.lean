import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1198Claim32134

noncomputable section

abbrev F3 := ZMod 3
abbrev V := Fin 6 → F3
abbrev Q := Fin 5 → F3

/-- A Cayley relation, with no inverse-closure restriction so that the same
    carrier covers both directed and ordinary undirected Cayley structures. -/
def cayleyRelation (S : Set V) (x y : V) : Prop :=
  y - x ∈ S

def relationAutomorphism (S : Set V) (e : Equiv.Perm V) : Prop :=
  ∀ x y : V,
    cayleyRelation S (e x) (e y) ↔ cayleyRelation S x y

def fullRelationAutomorphismSet (S : Set V) : Set (Equiv.Perm V) :=
  {e | relationAutomorphism S e}

/-- A common system of literal three-point blocks. -/
def threePointBlockSystem (q : V → Q) : Prop :=
  Function.Surjective q ∧
    ∀ b : Q, Set.ncard {x : V | q x = b} = 3

def blockPreserving (q : V → Q) (e : Equiv.Perm V) : Prop :=
  ∃ eq : Equiv.Perm Q, ∀ x : V, eq (q x) = q (e x)

/-- The set of full relation automorphisms that induce permutations on the
    supplied block quotient. -/
def blockStabilizer (S : Set V) (q : V → Q) :
    Set (Equiv.Perm V) :=
  {e | e ∈ fullRelationAutomorphismSet S ∧ blockPreserving q e}

/-- The actual permutation image of a set of block-preserving permutations. -/
def quotientImage (q : V → Q) (U : Set (Equiv.Perm V)) :
    Set (Equiv.Perm Q) :=
  {eq | ∃ e : Equiv.Perm V, e ∈ U ∧
    ∀ x : V, eq (q x) = q (e x)}

/-- Regularity on a literal permutation carrier. -/
def regularPermutationSubgroup {X : Type*}
    (R : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x y : X, ∃! r : Equiv.Perm X, r ∈ R ∧ r x = y

def regularC3SixCopy (R : Subgroup (Equiv.Perm V)) : Prop :=
  regularPermutationSubgroup R ∧
    Nonempty (R ≃* Multiplicative V)

/-- The actual induced quotient image is required to be the regular C₃⁵
    copy, rather than an abstract or enlarged quotient group. -/
def inducedRegularC3FiveCopy
    (q : V → Q) (R : Subgroup (Equiv.Perm V)) : Prop :=
  ∃ H : Subgroup (Equiv.Perm Q),
    (H : Set (Equiv.Perm Q)) =
      quotientImage q (R : Set (Equiv.Perm V)) ∧
    regularPermutationSubgroup H ∧
    Nonempty (H ≃* Multiplicative Q)

def quotientCopiesConjugateInActualImage
    (S : Set V) (q : V → Q)
    (R T : Subgroup (Equiv.Perm V)) : Prop :=
  ∃ eq : Equiv.Perm Q,
    eq ∈ quotientImage q (blockStabilizer S q) ∧
    ∀ h : Equiv.Perm Q,
      h ∈ quotientImage q (R : Set (Equiv.Perm V)) ↔
        eq * h * eq⁻¹ ∈
          quotientImage q (T : Set (Equiv.Perm V))

def regularCopiesConjugateInFullRelationAutomorphismSet
    (S : Set V) (R T : Subgroup (Equiv.Perm V)) : Prop :=
  ∃ e : Equiv.Perm V,
    e ∈ fullRelationAutomorphismSet S ∧
    ∀ r : Equiv.Perm V,
      r ∈ R ↔ e * r * e⁻¹ ∈ T

/-- The exact hypotheses and conclusion of the C₃⁶ literal
    quotient-alignment specialization. -/
def claim32134 : Prop :=
  ∀ (S : Set V) (q : V → Q)
    (R T : Subgroup (Equiv.Perm V)),
    threePointBlockSystem q ∧
      (∀ r : Equiv.Perm V,
        r ∈ R → relationAutomorphism S r ∧ blockPreserving q r) ∧
      (∀ t : Equiv.Perm V,
        t ∈ T → relationAutomorphism S t ∧ blockPreserving q t) ∧
      regularC3SixCopy R ∧
      regularC3SixCopy T ∧
      inducedRegularC3FiveCopy q R ∧
      inducedRegularC3FiveCopy q T ∧
      quotientCopiesConjugateInActualImage S q R T →
      regularCopiesConjugateInFullRelationAutomorphismSet S R T

end

end MathlibPlus.Open.ResearchFormalization.R1198Claim32134
