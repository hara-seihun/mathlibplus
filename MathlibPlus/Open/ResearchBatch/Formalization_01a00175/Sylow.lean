import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

noncomputable section
open Classical

abbrev PermSubgroup (Ω : Type*) := Subgroup (Equiv.Perm Ω)

def isRegularPermutationSubgroup {Ω : Type*} (R : PermSubgroup Ω) : Prop :=
  ∀ x y : Ω, ∃! r : R, r.1 x = y

def isPOrder {K : Type*} [Group K] [Fintype K]
    (p : ℕ) (P : Subgroup K) : Prop :=
  ∃ n : ℕ, Fintype.card P = p ^ n

def isSylowP {Ω : Type*} [Fintype Ω]
    (p : ℕ) (R P : PermSubgroup Ω) : Prop :=
  P ≤ R ∧ isPOrder p P ∧
    ∀ Q : PermSubgroup Ω, Q ≤ R → isPOrder p Q →
      Fintype.card Q ≤ Fintype.card P

def isUniqueSylowP {Ω : Type*} [Fintype Ω]
    (p : ℕ) (R P : PermSubgroup Ω) : Prop :=
  isSylowP p R P ∧ ∀ Q : PermSubgroup Ω, isSylowP p R Q → Q = P

def conjugatePermutationSubgroup {Ω : Type*}
    (x : Equiv.Perm Ω) (Q : PermSubgroup Ω) : PermSubgroup Ω :=
  Subgroup.map (MulAut.conj x) Q

def orbitPartition {Ω : Type*} [Fintype Ω]
    (P : PermSubgroup Ω) : Set (Set Ω) :=
  Set.range (fun ω : Ω => MulAction.orbit P ω)

def commonSylowOrbitAlignment : Prop :=
  ∀ (p m : ℕ) (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω]
    (R T : PermSubgroup Ω) (P Q : PermSubgroup Ω),
    Nat.Prime p → m < p → ¬ p ∣ m → Fintype.card G = m * p →
    isRegularPermutationSubgroup R → isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) → Nonempty (T ≃* G) →
    isUniqueSylowP p R P → isUniqueSylowP p T Q →
      ∃ x : Equiv.Perm Ω,
        x ∈ Subgroup.closure
          ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) ∧
        orbitPartition P =
          orbitPartition (conjugatePermutationSubgroup x Q)

def alternatingSubgroup (n : ℕ) : Subgroup (Equiv.Perm (Fin n)) :=
  MonoidHom.ker (Equiv.Perm.sign : Equiv.Perm (Fin n) →* ℤˣ)

def graphInvariant {V : Type*} (K : Subgroup (Equiv.Perm V))
    (Γ : SimpleGraph V) : Prop :=
  ∀ g : Equiv.Perm V, g ∈ K → ∀ v w : V,
    Γ.Adj (g v) (g w) ↔ Γ.Adj v w

def graphEmptyOrComplete {V : Type*} (Γ : SimpleGraph V) : Prop :=
  (∀ v w : V, ¬ Γ.Adj v w) ∨
    (∀ v w : V, v ≠ w → Γ.Adj v w)

def fullSymmetricGraphAutomorphisms {V : Type*} (Γ : SimpleGraph V) : Prop :=
  ∀ g : Equiv.Perm V, ∀ v w : V,
    Γ.Adj (g v) (g w) ↔ Γ.Adj v w

def invariantGraphCollapse300 : Prop :=
  ∀ Γ : SimpleGraph (Fin 300),
    (graphInvariant (alternatingSubgroup 300) Γ ∨
      graphInvariant (⊤ : Subgroup (Equiv.Perm (Fin 300))) Γ) →
      graphEmptyOrComplete Γ ∧ fullSymmetricGraphAutomorphisms Γ

def regularCopiesConjugateDegree105 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G]
    (R T : PermSubgroup (Fin 105)),
    isRegularPermutationSubgroup R → isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) → Nonempty (T ≃* G) →
      ∃ x : Equiv.Perm (Fin 105),
        T = conjugatePermutationSubgroup x R

def regularCopiesConjugateDegree300 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G]
    (R T : PermSubgroup (Fin 300)),
    isRegularPermutationSubgroup R → isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) → Nonempty (T ≃* G) →
      ∃ x : Equiv.Perm (Fin 300),
        T = conjugatePermutationSubgroup x R

def ambientSylowOrbitAlignment : Prop :=
  ∀ (p m : ℕ) (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω]
    (A R T : PermSubgroup Ω) (P Q : PermSubgroup Ω),
    Nat.Prime p → m < p → ¬ p ∣ m → Fintype.card G = m * p →
    isRegularPermutationSubgroup R → isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) → Nonempty (T ≃* G) →
    isUniqueSylowP p R P → isUniqueSylowP p T Q → R ≤ A → T ≤ A →
      ∃ x : Equiv.Perm Ω,
        x ∈ A ∧
        x ∈ Subgroup.closure
          ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) ∧
        orbitPartition P =
          orbitPartition (conjugatePermutationSubgroup x Q)

end

end MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow
