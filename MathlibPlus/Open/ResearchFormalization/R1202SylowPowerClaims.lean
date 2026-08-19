import MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

namespace MathlibPlus.Open.ResearchFormalization.R1202

open MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

/--
Claim 32180, source-bound to the two regular copies in R-1202: under the
large-prime order hypotheses, the designated Sylow subgroups of the copies
have order `p^a`, are unique in their copies, and are characteristic there.
-/
def sylowUniquenessInRegularCopies_claim32180 : Prop :=
  ∀ (p a m : ℕ) (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω]
    (R T : PermSubgroup Ω) (P Q : PermSubgroup Ω),
    letI : Fintype (Equiv.Perm Ω) := Fintype.ofFinite _
    letI : Fintype P := Fintype.ofFinite _
    letI : Fintype Q := Fintype.ofFinite _
    Nat.Prime p → 0 < a → m < p → ¬ p ∣ m →
    Fintype.card G = m * p ^ a →
    Fintype.card Ω = m * p ^ a →
    isRegularPermutationSubgroup R →
    isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) →
    Nonempty (T ≃* G) →
    isSylowP p R P →
    isSylowP p T Q →
    Fintype.card P = p ^ a ∧
      Fintype.card Q = p ^ a ∧
      (∀ P' : PermSubgroup Ω, isSylowP p R P' → P' = P) ∧
      (∀ Q' : PermSubgroup Ω, isSylowP p T Q' → Q' = Q) ∧
      (∀ φ : R ≃* R, ∀ r : R,
        ((r : Equiv.Perm Ω) ∈ P ↔
          ((φ r : R) : Equiv.Perm Ω) ∈ P)) ∧
      (∀ φ : T ≃* T, ∀ t : T,
        ((t : Equiv.Perm Ω) ∈ Q ↔
          ((φ t : T) : Equiv.Perm Ω) ∈ Q))

/--
Claim 32183, source-bound to the common ambient Sylow group in R-1202: after
an actual generated-group conjugation places the second designated Sylow
subgroup inside the same ambient `p`-group as the first, every ambient orbit
contains a first-copy orbit and has exactly `p^a` points.
-/
def orbitSizeSqueezeInsideCommonSylow_claim32183 : Prop :=
  ∀ (p a m : ℕ) (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω]
    (R T P Q U : PermSubgroup Ω) (x : Equiv.Perm Ω),
    letI : Fintype (Equiv.Perm Ω) := Fintype.ofFinite _
    letI : Fintype P := Fintype.ofFinite _
    letI : Fintype Q := Fintype.ofFinite _
    letI : Fintype U := Fintype.ofFinite _
    Nat.Prime p → 0 < a → m < p → ¬ p ∣ m →
    Fintype.card G = m * p ^ a →
    Fintype.card Ω = m * p ^ a →
    isRegularPermutationSubgroup R →
    isRegularPermutationSubgroup T →
    Nonempty (R ≃* G) →
    Nonempty (T ≃* G) →
    isSylowP p R P →
    isSylowP p T Q →
    x ∈ Subgroup.closure
      ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) →
    U ≤ Subgroup.closure
      ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) →
    P ≤ U →
    conjugatePermutationSubgroup x Q ≤ U →
    isPOrder p U →
    ∀ ω : Ω,
      MulAction.orbit P ω ⊆ MulAction.orbit U ω ∧
        (MulAction.orbit U ω).ncard = p ^ a

end MathlibPlus.Open.ResearchFormalization.R1202
