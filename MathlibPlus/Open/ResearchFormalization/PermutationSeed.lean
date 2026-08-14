import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.PermutationSeed

def fixedPointFree {α : Type*} (u : Equiv.Perm α) : Prop :=
  ∀ x, u x ≠ x

def involution {α : Type*} (u : Equiv.Perm α) : Prop :=
  u ^ 2 = 1

def semiregularOrderEight (u : Equiv.Perm (Fin 16)) : Prop :=
  orderOf u = 8 ∧
    ∀ k : Fin 8, k ≠ 0 → fixedPointFree (u ^ (k : ℕ))

def seedCyclicCycle (c : Equiv.Perm (Fin 16)) : Prop :=
  c 0 = 8 ∧ c 8 = 1 ∧ c 1 = 9 ∧ c 9 = 2 ∧
  c 2 = 10 ∧ c 10 = 3 ∧ c 3 = 11 ∧ c 11 = 0 ∧
  c 4 = 12 ∧ c 12 = 5 ∧ c 5 = 13 ∧ c 13 = 6 ∧
  c 6 = 14 ∧ c 14 = 7 ∧ c 7 = 15 ∧ c 15 = 4

def seedDCyclicCycle (d : Equiv.Perm (Fin 16)) : Prop :=
  d 0 = 8 ∧ d 8 = 1 ∧ d 1 = 9 ∧ d 9 = 4 ∧
  d 4 = 12 ∧ d 12 = 5 ∧ d 5 = 13 ∧ d 13 = 0 ∧
  d 2 = 10 ∧ d 10 = 3 ∧ d 3 = 11 ∧ d 11 = 6 ∧
  d 6 = 14 ∧ d 14 = 7 ∧ d 7 = 15 ∧ d 15 = 2

def seedGeneratedSubgroup (c d : Equiv.Perm (Fin 16)) :
    Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure ({c, d} : Set (Equiv.Perm (Fin 16)))

def isPermutationTwoGroup (K : Subgroup (Equiv.Perm (Fin 16))) : Prop :=
  ∃ r : ℕ, Nat.card K = 2 ^ r

/-- The exact order-eight seed, including the two displayed cycles and the
order-128 generated permutation 2-group. -/
def orderEightSeed : Prop :=
  ∃ c d : Equiv.Perm (Fin 16),
    seedCyclicCycle c ∧
    seedDCyclicCycle d ∧
    semiregularOrderEight c ∧
    semiregularOrderEight d ∧
    c ^ 4 ≠ d ^ 4 ∧
    fixedPointFree (c ^ 4) ∧
    involution (c ^ 4) ∧
    fixedPointFree (d ^ 4) ∧
    involution (d ^ 4) ∧
    Nat.card (seedGeneratedSubgroup c d) = 128 ∧
    isPermutationTwoGroup (seedGeneratedSubgroup c d) ∧
    Subgroup.closure ({c} : Set (Equiv.Perm (Fin 16))) ≤ seedGeneratedSubgroup c d ∧
    Subgroup.closure ({d} : Set (Equiv.Perm (Fin 16))) ≤ seedGeneratedSubgroup c d

end MathlibPlus.Open.ResearchFormalization.PermutationSeed
