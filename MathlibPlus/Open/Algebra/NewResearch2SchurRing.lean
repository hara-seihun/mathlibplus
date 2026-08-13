import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

open scoped BigOperators

namespace MathlibPlus.Open.Algebra
noncomputable section
open Classical
structure SchurRingData (G : Type*) [Fintype G] [DecidableEq G] [Group G] where
  basicSets : Finset (Finset G)
  partition : ∀ ⦃A B : Finset G⦄, A ∈ basicSets → B ∈ basicSets → A = B ∨ Disjoint A B
  covers : basicSets.biUnion id = Finset.univ
  identity_mem : ∃ T ∈ basicSets, T = ({1} : Finset G)
  inverse_closed : ∀ T ∈ basicSets, T.image (·⁻¹) ∈ basicSets
  structureConstants : Prop
structure NormalSSubgroup {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) where
  carrier : Finset G
  subgroup : ∃ H : Subgroup G, carrier = H.carrier.toFinset
  normal : Prop
  unionBasic : ∀ T ∈ S.basicSets, T ⊆ carrier ∨ Disjoint T carrier
structure SSubgroup {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) where
  carrier : Finset G
  subgroup : ∃ H : Subgroup G, carrier = H.carrier.toFinset
  unionBasic : ∀ T ∈ S.basicSets, T ⊆ carrier ∨ Disjoint T carrier
def normalSSubgroup_claim28131 : Prop := ∀ {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) (H : NormalSSubgroup S), ∃ (N : Subgroup G), H.carrier = N.carrier.toFinset ∧ H.normal
def rightCosetUnion {G : Type*} [Fintype G] [DecidableEq G] [Group G] (H T : Finset G) : Prop := ∀ x ∈ T, ∀ h₁ ∈ H, ∀ h₂ ∈ H, x * h₁ ∈ T ↔ x * h₂ ∈ T
def outsideKHCosetSaturation {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) (H K : Finset G) : Prop := H ⊆ K ∧ H.Nonempty ∧ ∀ T ∈ S.basicSets, ¬ T ⊆ K → rightCosetUnion H T
def outsideKHCosetSaturation_claim28132 : Prop := ∀ {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) (H K : Finset G), H ⊆ K → H.Nonempty → outsideKHCosetSaturation S H K
def wedgeProductData {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) (H K : Finset G) : Prop := outsideKHCosetSaturation S H K ∧ ∃ S₁ S₂ : SchurRingData G, S₁.basicSets.Nonempty ∧ S₂.basicSets.Nonempty ∧ ∃ T₁ ∈ S₁.basicSets, T₁ ⊆ K
def wedgeProductCriterion_claim28133 : Prop := ∀ {G : Type*} [Fintype G] [DecidableEq G] [Group G] (S : SchurRingData G) (H K : Finset G), H ⊆ K → H.Nonempty → K.Nonempty → outsideKHCosetSaturation S H K → wedgeProductData S H K
def cyclicTwelveWedgeExample_claim28135 : Prop := ∃ S : SchurRingData (Multiplicative (ZMod 12)), ∃ H K : Finset (Multiplicative (ZMod 12)), H.Nonempty ∧ K.Nonempty ∧ outsideKHCosetSaturation S H K ∧ S.basicSets.Nonempty ∧ S.structureConstants
end
end MathlibPlus.Open.Algebra
