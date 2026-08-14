import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- A permutation subgroup is regular when there is exactly one element sending
any point to any other point. -/
def IsRegularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! h : H, h.1 x = y

/-- The permutation `p` conjugates `R` onto `T`. -/
def ConjugatesPermutationSubgroups {Ω : Type*}
    (p : Equiv.Perm Ω) (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g : Equiv.Perm Ω,
    g ∈ T ↔ ∃ r : Equiv.Perm Ω, r ∈ R ∧ g = p * r * p⁻¹

/-- The unordered orbital of a two-point set under a permutation subgroup. -/
def UnorderedOrbital {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (s : Finset Ω) : Set (Finset Ω) :=
  {t | t.card = 2 ∧ ∃ g : Equiv.Perm Ω, g ∈ X ∧ t = s.map g.toEmbedding}

/-- `p` fixes every unordered orbital setwise. -/
def FixesEveryUnorderedOrbital {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (p : Equiv.Perm Ω) : Prop :=
  ∀ s : Finset Ω, s.card = 2 →
    ∀ t : Finset Ω,
      t ∈ UnorderedOrbital X s ↔
        t.map p.toEmbedding ∈ UnorderedOrbital X s

/-- An undirected graph represented by its two-element vertex sets. -/
def IsUndirectedGraph {Ω : Type*} (E : Set (Finset Ω)) : Prop :=
  ∀ s ∈ E, s.card = 2

/-- Invariance of an undirected graph under a permutation subgroup. -/
def IsInvariantUnder {Ω : Type*}
    (E : Set (Finset Ω)) (X : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g : Equiv.Perm Ω, g ∈ X →
    ∀ s : Finset Ω, s.card = 2 →
      (s ∈ E ↔ s.map g.toEmbedding ∈ E)

/-- A permutation is an automorphism of an undirected graph. -/
def IsGraphAutomorphism {Ω : Type*}
    (E : Set (Finset Ω)) (p : Equiv.Perm Ω) : Prop :=
  ∀ s : Finset Ω, s.card = 2 →
    (s ∈ E ↔ s.map p.toEmbedding ∈ E)

/-- Claim 39651: an orbital-fixing transporter is an automorphism of every
undirected graph invariant under the generated group. -/
def claim39651 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω]
    (R T : Subgroup (Equiv.Perm Ω)) (p : Equiv.Perm Ω),
    IsRegularPermutationSubgroup R →
    IsRegularPermutationSubgroup T →
    ConjugatesPermutationSubgroups p R T →
    FixesEveryUnorderedOrbital (R ⊔ T) p →
    ∀ E : Set (Finset Ω),
      IsUndirectedGraph E →
      IsInvariantUnder E (R ⊔ T) →
      IsGraphAutomorphism E p

end MathlibPlus.Open.ResearchFormalization
