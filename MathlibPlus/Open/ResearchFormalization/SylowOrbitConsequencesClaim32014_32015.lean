import MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

namespace MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

noncomputable section
open Classical

/-- Claims 32014 and 41784: in the full regular-copy Sylow setup, every
p-subgroup of the generated group containing the designated Sylow subgroup P
has exactly the P-orbits as its orbits when the total degree is mp with m < p. -/
def smallTotalDegreeForcesSylowOrbits : Prop :=
  ∀ (p m : ℕ) (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω]
    (R T : PermSubgroup Ω) (P Q : PermSubgroup Ω),
    Nat.Prime p → m < p → ¬ p ∣ m → Fintype.card G = m * p →
    Fintype.card Ω = m * p →
    isRegularPermutationSubgroup R → isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) → Nonempty (T ≃* G) →
    isUniqueSylowP p R P → isUniqueSylowP p T Q →
    ∀ (U : PermSubgroup Ω),
      U ≤ Subgroup.closure
        ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) →
      P ≤ U → isPOrder p U →
      ∀ ω : Ω,
        (∃ η : Ω, MulAction.orbit P η ⊆ MulAction.orbit U ω) ∧
          p ∣ (MulAction.orbit U ω).ncard ∧
          (MulAction.orbit U ω).ncard < p ^ 2 ∧
          (MulAction.orbit U ω).ncard = p ∧
          ∃ η : Ω, MulAction.orbit U ω = MulAction.orbit P η

/-- Claims 32015 and 41785: the common Sylow-orbit partition is the one
produced by an actual generated-group conjugator and has exactly m blocks,
each of cardinality p. -/
def commonSylowPartitionHasMPBlocks : Prop :=
  ∀ (p m : ℕ) (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω]
    (R T : PermSubgroup Ω) (P Q : PermSubgroup Ω),
    Nat.Prime p → m < p → ¬ p ∣ m → Fintype.card G = m * p →
    Fintype.card Ω = m * p →
    isRegularPermutationSubgroup R → isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) → Nonempty (T ≃* G) →
    isUniqueSylowP p R P → isUniqueSylowP p T Q →
      ∃ x : Equiv.Perm Ω,
        x ∈ Subgroup.closure
          ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) ∧
        orbitPartition P =
          orbitPartition (conjugatePermutationSubgroup x Q) ∧
        Set.ncard (orbitPartition P) = m ∧
        ∀ B : Set Ω, B ∈ orbitPartition P → B.ncard = p

end

end MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow
