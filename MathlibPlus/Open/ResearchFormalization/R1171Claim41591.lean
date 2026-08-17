import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41591

noncomputable section

abbrev Permutation (Ω : Type*) := Equiv.Perm Ω
abbrev ElementaryAbelian (p n : ℕ) := Fin n → Multiplicative (ZMod p)

def regularPermutationCopy {Ω : Type*}
    (R : Subgroup (Permutation Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Permutation Ω) x = y

def abelianPermutationCopy {Ω : Type*}
    (R : Subgroup (Permutation Ω)) : Prop :=
  ∀ r s : R,
    (r : Permutation Ω) * (s : Permutation Ω) =
      (s : Permutation Ω) * (r : Permutation Ω)

def centralInAmbient {Ω : Type*}
    (P D : Subgroup (Permutation Ω)) : Prop :=
  ∀ d : D, ∀ q : P,
    (d : Permutation Ω) * (q : Permutation Ω) =
      (q : Permutation Ω) * (d : Permutation Ω)

def hasElementaryAbelianType {G : Type*} [Group G]
    (H : Subgroup G) (p n : ℕ) : Prop :=
  Nonempty (H ≃* ElementaryAbelian p n)

def conjugateSubgroup {Ω : Type*}
    (x : Permutation Ω) (H : Subgroup (Permutation Ω)) :
    Subgroup (Permutation Ω) :=
  Subgroup.map ((MulAut.conj x).toMonoidHom) H

def dOrbit {Ω : Type*}
    (D : Subgroup (Permutation Ω)) (x : Ω) : Set Ω :=
  {y | ∃ d : D, (d : Permutation Ω) x = y}

def dOrbitBlocks {Ω : Type*}
    (D : Subgroup (Permutation Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, B = dOrbit D x}

def permutesBlockPartition {Ω : Type*}
    (P : Subgroup (Permutation Ω)) (blocks : Set (Set Ω)) : Prop :=
  ∀ p : P,
    Set.image (fun B : Set Ω => (p : Permutation Ω) '' B) blocks = blocks

def dOrbitBlockSystem {Ω : Type*}
    (D P : Subgroup (Permutation Ω)) (blocks : Set (Set Ω)) : Prop :=
  blocks = dOrbitBlocks D ∧ permutesBlockPartition P blocks

/-- The actual ambient normalizer `N_A(D)`. -/
def normalizerWithin {Ω : Type*}
    (A D : Subgroup (Permutation Ω)) : Subgroup (Permutation Ω) :=
  A ⊓ Subgroup.normalizer (D : Set (Permutation Ω))

/-- Equality of the induced quotient actions after conjugating the source
copy by `a`; this compares actions on blocks, not arbitrary abstract groups. -/
def quotientBlockConjugates {Ω : Type*}
    (a : Permutation Ω)
    (R S : Subgroup (Permutation Ω)) (blocks : Set (Set Ω)) : Prop :=
  (∀ r : R, ∃ s : S, ∀ B : Set Ω, B ∈ blocks →
    (a * (r : Permutation Ω) * a⁻¹) '' B =
      (s : Permutation Ω) '' B) ∧
    (∀ s : S, ∃ r : R, ∀ B : Set Ω, B ∈ blocks →
      (s : Permutation Ω) '' B =
        (a * (r : Permutation Ω) * a⁻¹) '' B)

/-- A normalized isomorphism is literal identity on the common D and on the
quotient block action; its remaining discrepancy is D-valued. -/
def normalizedDValuedBlockTranslation {Ω : Type*}
    (R S D : Subgroup (Permutation Ω)) (blocks : Set (Set Ω))
    (φ : R ≃* S) : Prop :=
  (∀ d : D, ∃ r : R,
    (r : Permutation Ω) = (d : Permutation Ω) ∧
      (φ r : Permutation Ω) = (d : Permutation Ω)) ∧
    (∀ r : R, ∀ B : Set Ω, B ∈ blocks →
      (φ r : Permutation Ω) '' B = (r : Permutation Ω) '' B) ∧
      (∀ r : R, ∃ d : D,
        (φ r : Permutation Ω) =
          (r : Permutation Ω) * (d : Permutation Ω))

/-- Claim 41591: an element of the actual normalizer can be used to align the
induced quotient copies; the aligned copies contain the same literal D, have
identity normalized quotient action, and differ only by D-valued translations.
-/
def claim41591 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] (p n : ℕ)
    (A P R S D : Subgroup (Permutation Ω))
    (blocks : Set (Set Ω)),
    Nat.Prime p → 1 ≤ n →
      P ≤ A ∧ R ≤ P ∧ S ≤ P ∧
        regularPermutationCopy R ∧ abelianPermutationCopy R ∧
          regularPermutationCopy S ∧ abelianPermutationCopy S ∧
            IsPGroup p R ∧ IsPGroup p S ∧
              hasElementaryAbelianType R p n ∧
                hasElementaryAbelianType S p n ∧
                  centralInAmbient P D ∧ Nat.card D = p ∧
                    D ≤ R ∧ D ≤ S ∧ dOrbitBlockSystem D P blocks →
      ∀ a : normalizerWithin A D,
        quotientBlockConjugates (a : Permutation Ω) R S blocks →
          D ≤ conjugateSubgroup (a : Permutation Ω) R ∧
            ∃ φ : conjugateSubgroup (a : Permutation Ω) R ≃* S,
              normalizedDValuedBlockTranslation
                (conjugateSubgroup (a : Permutation Ω) R) S D blocks φ

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41591
