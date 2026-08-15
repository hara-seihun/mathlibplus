import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1333

noncomputable section

def transitivePermutationGroup {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y, ∃ g, g ∈ G ∧ g x = y

def regularCyclicGenerator {Ω : Type*}
    [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (N : ℕ)
    (c : Equiv.Perm Ω) : Prop :=
  c ∈ G ∧ orderOf c = N ∧
    ∀ x y, ∃! k : Fin N, (c ^ (k.1 : ℕ)) x = y

def imprimitivePermutationGroup {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ B : Finset Ω,
    1 < B.card ∧ B.card < Fintype.card Ω ∧
      ∀ g ∈ G,
        Disjoint B (B.image g) ∨ B.image g = B

def twoTransitivePermutationGroup {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y x' y', x ≠ y → x' ≠ y' →
    ∃ g, g ∈ G ∧ g x = x' ∧ g y = y'

/-- A transitive group of distinct-prime-product degree with a regular cyclic subgroup
is imprimitive or 2-transitive. -/
def primeProductCyclicDichotomy {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p q : ℕ) (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
    Fintype.card Ω = p * q →
    (transitivePermutationGroup G ∧
      ∃ c : Equiv.Perm Ω, regularCyclicGenerator G (p * q) c) →
      imprimitivePermutationGroup G ∨ twoTransitivePermutationGroup G

def rightTranslate {C : Type*} [Group C] [DecidableEq C]
    (B : Finset C) (c : C) : Finset C :=
  B.image (fun b => b * c)

/-- Under the regular identification Ω=C, a block through 1 is a subgroup carrier;
translating by a point of the block meets the block and therefore fixes it. -/
def regularBlockCorrespondsToSubgroup {C : Type*} [Fintype C] [DecidableEq C]
    [Group C] (B : Finset C) : Prop :=
  1 ∈ B ∧
    (∀ c, Disjoint B (rightTranslate B c) ∨ rightTranslate B c = B) ∧
    (∀ c ∈ B,
      (rightTranslate B c ∩ B).Nonempty ∧ rightTranslate B c = B ∧
        ∃ H : Subgroup C, ∀ x, x ∈ B ↔ x ∈ H)

end

end MathlibPlus.Open.ResearchFormalization.R1333
