import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedc64ac79c92719c0ad336498c

def IsDoubleTransposition (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∃ a b c d : Fin 4,
    a ≠ b ∧ c ≠ d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      σ = Equiv.swap a b * Equiv.swap c d

def preservesFinset (σ : Equiv.Perm α) (S : Finset α) : Prop :=
  ∀ x, x ∈ S ↔ σ x ∈ S

/-- Claim 12654: invariance under a product of two double transpositions does
not imply invariance under either factor. -/
def claim12654 : Prop :=
  ∃ S : Finset (Fin 4),
    let a : Equiv.Perm (Fin 4) :=
      Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3
    let b : Equiv.Perm (Fin 4) :=
      Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3
    S = ({(0 : Fin 4), 3} : Finset (Fin 4)) ∧
      IsDoubleTransposition a ∧
      IsDoubleTransposition b ∧
      preservesFinset (a * b) S ∧
      ¬ preservesFinset a S ∧
      ¬ preservesFinset b S

end MathlibPlus.Open.ResearchFormalizationBatch019ffedc64ac79c92719c0ad336498c
