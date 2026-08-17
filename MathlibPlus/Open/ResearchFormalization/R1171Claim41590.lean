import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41590

noncomputable section

abbrev Permutation (Ω : Type*) := Equiv.Perm Ω

def regularPermutationCopy {Ω : Type*}
    (R : Subgroup (Permutation Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Permutation Ω) x = y

def abelianPermutationCopy {Ω : Type*}
    (R : Subgroup (Permutation Ω)) : Prop :=
  ∀ r s : R,
    (r : Permutation Ω) * (s : Permutation Ω) =
      (s : Permutation Ω) * (r : Permutation Ω)

def conjugateSubgroup {Ω : Type*}
    (x : Permutation Ω) (H : Subgroup (Permutation Ω)) :
    Subgroup (Permutation Ω) :=
  Subgroup.map ((MulAut.conj x).toMonoidHom) H

def generatedPair {Ω : Type*}
    (R T : Subgroup (Permutation Ω)) : Subgroup (Permutation Ω) :=
  Subgroup.closure ((R : Set (Permutation Ω)) ∪
    (T : Set (Permutation Ω)))

/-- An ordered-pair orbit of a permutation subgroup. -/
def orderedPairOrbit {Ω : Type*}
    (X : Subgroup (Permutation Ω)) (p : Ω × Ω) : Set (Ω × Ω) :=
  {q | ∃ g : X,
    ((g : Permutation Ω) p.1, (g : Permutation Ω) p.2) = q}

/-- The exact two-closure carrier: every ordered-pair orbit is fixed
setwise, not merely permuted with another orbit. -/
def twoClosure {Ω : Type*}
    (X : Subgroup (Permutation Ω)) : Set (Permutation Ω) :=
  {q | ∀ p : Ω × Ω,
    Set.image (fun z : Ω × Ω => (q z.1, q z.2))
      (orderedPairOrbit X p) = orderedPairOrbit X p}

def containedInOwnTwoClosure {Ω : Type*}
    (X : Subgroup (Permutation Ω)) : Prop :=
  ∀ g : X, (g : Permutation Ω) ∈ twoClosure X

def twoClosedAmbient {Ω : Type*}
    (A : Subgroup (Permutation Ω)) : Prop :=
  ∀ q : Permutation Ω, q ∈ twoClosure A → q ∈ A

def conjugateInAmbient {Ω : Type*}
    (A R T : Subgroup (Permutation Ω)) : Prop :=
  ∃ a : A, conjugateSubgroup (a : Permutation Ω) R = T

/-- Claim 41590: the generated group lies in its exact two-closure, and an
x from that generated group can replace T by T^x without changing conjugacy
of the two regular copies inside the relevant 2-closed ambient group. -/
def claim41590 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω]
    (R T X A : Subgroup (Permutation Ω)),
    regularPermutationCopy R ∧ abelianPermutationCopy R ∧
      regularPermutationCopy T ∧ abelianPermutationCopy T ∧
        X = generatedPair R T ∧ R ≤ A ∧ T ≤ A ∧ X ≤ A ∧
          twoClosedAmbient A →
      containedInOwnTwoClosure X ∧
        ∀ x : Permutation Ω, x ∈ X →
          (conjugateInAmbient A R T ↔
            conjugateInAmbient A R (conjugateSubgroup x T))

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41590
