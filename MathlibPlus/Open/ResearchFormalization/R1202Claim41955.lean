import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1202Claim41955

noncomputable section

private abbrev Perm (Ω : Type*) := Equiv.Perm Ω

private def regularPermutationCopy
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
    (R : Subgroup (Perm Ω)) : Prop :=
  ∃ e : G ≃* R,
    ∀ u v : Ω, ∃! g : G,
      ((e g : R) : Perm Ω) u = v

private def commonLargePrimeSetup
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
    (p m a : ℕ) (R T : Subgroup (Perm Ω)) : Prop :=
  Nat.Prime p ∧
    1 ≤ a ∧
      m < p ∧
        ¬ p ∣ m ∧
          Nat.card G = m * p ^ a ∧
            Nat.card Ω = m * p ^ a ∧
              regularPermutationCopy (G := G) R ∧
                regularPermutationCopy (G := G) T

private def pGroup
    {Ω : Type*} [Fintype Ω]
    (p : ℕ) (H : Subgroup (Perm Ω)) : Prop :=
  ∀ h : H, ∃ k : ℕ, orderOf (h : Perm Ω) = p ^ k

private def isSylow
    {Ω : Type*} [Fintype Ω]
    (p : ℕ) (X P : Subgroup (Perm Ω)) : Prop :=
  P ≤ X ∧
    pGroup p P ∧
      ∀ S : Subgroup (Perm Ω), S ≤ X → pGroup p S →
        Nat.card S ≤ Nat.card P

private def uniqueSylowInCopy
    {Ω : Type*} [Fintype Ω]
    (p a : ℕ) (R P : Subgroup (Perm Ω)) : Prop :=
  isSylow p R P ∧
    Nat.card P = p ^ a ∧
      ∀ S : Subgroup (Perm Ω), isSylow p R S → S = P

private def generatedPair
    {Ω : Type*}
    (R T : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure ((R : Set (Perm Ω)) ∪ (T : Set (Perm Ω)))

private def conjugateSubgroup
    {Ω : Type*}
    (H : Subgroup (Perm Ω)) (x : Perm Ω) : Subgroup (Perm Ω) :=
  Subgroup.map ((MulAut.conj x).toMonoidHom) H

private def orbitSet
    {Ω : Type*}
    (H : Subgroup (Perm Ω)) (u : Ω) : Set Ω :=
  {v | ∃ h : H, (h : Perm Ω) u = v}

private def orbitFamily
    {Ω : Type*}
    (H : Subgroup (Perm Ω)) : Set (Set Ω) :=
  Set.range (orbitSet H)

private def commonSylowOrbitContext
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
    (p m a : ℕ) (R T P Q U : Subgroup (Perm Ω))
    (x : Perm Ω) : Prop :=
  commonLargePrimeSetup (G := G) p m a R T ∧
    uniqueSylowInCopy p a R P ∧
      uniqueSylowInCopy p a T Q ∧
        isSylow p (generatedPair R T) U ∧
          P ≤ U ∧
            x ∈ generatedPair R T ∧
              conjugateSubgroup Q x ≤ U

/-- Claim 41955: under the common regular-copy and ambient-Sylow context,
the P, U, and conjugated Q orbit families coincide, and the common partition
has exactly m blocks, each of size p^a. -/
def claim41955 : Prop :=
  ∀ {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
    (p m a : ℕ) (R T P Q U : Subgroup (Perm Ω)) (x : Perm Ω),
    commonSylowOrbitContext (G := G) p m a R T P Q U x →
      orbitFamily P = orbitFamily U ∧
        orbitFamily U = orbitFamily (conjugateSubgroup Q x) ∧
          Set.ncard (orbitFamily U) = m ∧
            (∀ B : Set Ω, B ∈ orbitFamily U → Set.ncard B = p ^ a)

end

end MathlibPlus.Open.ResearchFormalization.R1202Claim41955
