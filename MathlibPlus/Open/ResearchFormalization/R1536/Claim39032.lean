import Mathlib
import MathlibPlus.Open.GraphTheory.R0943
import MathlibPlus.Open.ResearchBatch.R1536

namespace MathlibPlus.Open.ResearchFormalization.R1536

abbrev Q8 := QuaternionGroup 2
abbrev QuotientV4 := MathlibPlus.Open.GraphTheory.R0943.V4Group

/-- The section of a connection set above a quotient element of the odd factor. -/
def quaternionSection {A : Type*} {S : Set (A × Q8)} (a : A) : Set Q8 :=
  {q | (a, q) ∈ S}

/-- The multiset of all quaternion-section cardinalities, indexed by the odd factor. -/
noncomputable def quaternionSectionSizes {A : Type*} [Fintype A]
    (S : Set (A × Q8)) : Multiset ℕ :=
  Multiset.map (fun a : A => (quaternionSection (S := S) a).ncard)
    (Finset.univ : Finset A).1

/-- Preservation of the odd Hall factor and the Sylow-two factor, together with
    the resulting product splitting, for an automorphism of `A × Q₈`. -/
def preservesQuaternionProductFactors {A : Type*} [Group A]
    (φ : (A × Q8) ≃* (A × Q8)) : Prop :=
  ∃ φA : A ≃* A, ∃ φQ : Q8 ≃* Q8,
    (∀ a : A, φ (a, 1) = (φA a, 1)) ∧
      (∀ q : Q8, φ (1, q) = (1, φQ q)) ∧
      (∀ a : A, ∀ q : Q8, φ (a, q) = (φA a, φQ q))

/-- Doubling the colors records the section sizes supplied by the two-element
    fibres of the quaternion-to-`V₄` quotient. -/
noncomputable def doubledColorMultiset {A : Type*} [Fintype A]
    (c : A → Fin 5) : Multiset ℕ :=
  Multiset.map (fun k : Fin 5 => 2 * k.val)
    ((Finset.univ : Finset A).1.map c)

/-- Claim 39032: odd-Hall/Sylow-two automorphisms split, the central quotient
    lift has section size `2 * c(a)`, and the resulting section-size multiset is
    invariant under group automorphisms. -/
def claim39032 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    (∀ φ : (A × Q8) ≃* (A × Q8),
      preservesQuaternionProductFactors φ) ∧
    ∀ (c : A → Fin 5),
      MathlibPlus.Open.ResearchBatch.R1536.SymmetricFiveColorStructure c →
      ∀ (π : Q8 →* QuotientV4) (F : Fin 5 → Set QuotientV4),
        MathlibPlus.Open.GraphTheory.R0943.quaternionProjectionData π →
        (∀ k : Fin 5, Set.ncard (F k) = k.val) →
        let S := MathlibPlus.Open.GraphTheory.R0943.quaternionLiftedSet π F c
        (∀ a : A,
            (quaternionSection (S := S) a).ncard = 2 * (c a).val) ∧
          quaternionSectionSizes S = doubledColorMultiset c ∧
          (∀ φ : (A × Q8) ≃* (A × Q8),
            quaternionSectionSizes (Set.image φ S) = quaternionSectionSizes S)

end MathlibPlus.Open.ResearchFormalization.R1536
