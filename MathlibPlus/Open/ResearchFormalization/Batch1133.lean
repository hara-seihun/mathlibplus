import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch1133

/-- The derived subgroup, as a subgroup of its ambient group. -/
def derivedSubgroup (H : Type*) [Group H] : Subgroup H :=
  ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆

/-- Regularity for a subgroup of a permutation group. -/
def IsRegularSubgroup {Ω : Type*} [Fintype Ω]
    (S : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! s : S, s.1 x = y

/-- Regularity for a subgroup of a permutation subgroup K. -/
def IsRegularSubgroupOf {Ω : Type*} [Fintype Ω]
    (K : Subgroup (Equiv.Perm Ω)) (T : Subgroup K) : Prop :=
  ∀ x y : Ω, ∃! t : T, t.1.1 x = y

/-- The normalizer of P inside K, represented as an intersection of subgroups. -/
def normalizerWithin {Ω : Type*} (K P : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  K ⊓ Subgroup.normalizer (P : Set (Equiv.Perm Ω))

/-- A finite group is a p-group when its cardinality is a power of p. -/
def IsPSubgroup (p : ℕ) {H : Type*} [Finite H] [Group H] : Prop :=
  ∃ n : ℕ, Nat.card H = p ^ n

/--
Claim 30069: a regular target isomorphic to G has derived subgroup isomorphic
 to G's derived subgroup, and a prime derived order is preserved.
-/
def claim30069 : Prop :=
  ∀ {Ω G : Type*} [Fintype Ω] [Group G] [Finite G]
    (K : Subgroup (Equiv.Perm Ω)) (T : Subgroup K),
    IsRegularSubgroupOf K T →
    Nonempty (T ≃* G) →
      Nonempty (derivedSubgroup T ≃* derivedSubgroup G) ∧
        ∀ p : ℕ, Nat.Prime p →
          Nat.card (derivedSubgroup G) = p →
            Nat.card (derivedSubgroup T) = p

/--
Claim 30071: once the derived subgroups of regular copies R and T have been
 aligned to P, the target T lies in the normalizer of P inside K.
-/
def claim30071 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω]
    (K R T P : Subgroup (Equiv.Perm Ω)),
    IsRegularSubgroup R → IsRegularSubgroup T →
    R ≤ K → T ≤ K →
    ⁅R, R⁆ = P →
    ⁅T, T⁆ = P →
    T ≤ normalizerWithin K P

/--
Claim 30072: with a prime-order P and p² not dividing K, P is the unique
 p-subgroup in its normalizer, and every regular target of the specified
 isomorphism type inside that normalizer has derived subgroup P.
-/
def claim30072 : Prop :=
  ∀ {Ω G : Type*} [Fintype Ω] [Group G] [Finite G]
    (K P : Subgroup (Equiv.Perm Ω)) (p : ℕ),
    Nat.Prime p →
    P ≤ K →
    Nat.card P = p →
    ¬p ^ 2 ∣ Nat.card K →
    let N := normalizerWithin K P
    P ≤ N ∧
      N ≤ Subgroup.normalizer (P : Set (Equiv.Perm Ω)) ∧
      (∀ Q : Subgroup (Equiv.Perm Ω),
        Q ≤ N → IsPSubgroup p (H := Q) → Q ≤ P) ∧
      (∀ H : Subgroup (Equiv.Perm Ω),
        H ≤ N →
        IsRegularSubgroup H →
        Nonempty (H ≃* G) →
        Nat.card (derivedSubgroup G) = p →
          ⁅H, H⁆ = P)

end MathlibPlus.Open.ResearchFormalizationBatch1133
