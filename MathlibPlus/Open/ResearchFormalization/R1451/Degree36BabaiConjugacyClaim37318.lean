import Mathlib
import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.Open.ResearchFormalization.R1451.Degree36BabaiConjugacyClaim37318

private abbrev GroupCarrier :=
  Multiplicative ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3))
private abbrev Ω := Fin 72
private abbrev PermutationGroup := Subgroup (Equiv.Perm Ω)

private def regularCopy (R : PermutationGroup) : Prop :=
  Nonempty (R ≃* GroupCarrier) ∧
  ∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y

private def generatedGroup (R T : PermutationGroup) : PermutationGroup :=
  R ⊔ T

private def transitive (G : PermutationGroup) : Prop :=
  ∀ x y : Ω, ∃ g : G, (g : Equiv.Perm Ω) x = y

private def nontrivialBlock
    (G : PermutationGroup) (A : Set Ω) : Prop :=
  A.Nonempty ∧ A ≠ Set.univ ∧ 2 ≤ A.ncard ∧
    ∀ g : G,
      Set.image (g : Equiv.Perm Ω) A = A ∨
        Disjoint (Set.image (g : Equiv.Perm Ω) A) A

private def twoBlockMinimum
    (G : PermutationGroup) (P : Finset (Set Ω)) : Prop :=
  P.card = 2 ∧
  (∀ A ∈ P, A.ncard = 36) ∧
  (∀ x : Ω, ∃ A ∈ P, x ∈ A) ∧
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
  (∀ g : G, ∀ A ∈ P,
    Set.image (g : Equiv.Perm Ω) A ∈ P) ∧
  (∀ A : Set Ω, nontrivialBlock G A → 36 ≤ A.ncard)

private def locallyPrimitive
    (G : PermutationGroup) (B : Set Ω) : Prop :=
  B.Nonempty ∧
  (∀ x ∈ B, ∀ y ∈ B,
    ∃ g : G,
      Set.image (g : Equiv.Perm Ω) B = B ∧
      (g : Equiv.Perm Ω) x = y) ∧
  (∀ A : Set Ω,
    A ⊆ B → A.Nonempty → A ≠ B →
    ¬ (∀ g : G,
      Set.image (g : Equiv.Perm Ω) B = B →
        Set.image (g : Equiv.Perm Ω) A = A))

private def locallyTwoTransitive
    (G : PermutationGroup) (B : Set Ω) : Prop :=
  ∀ x y x' y' : Ω,
    x ∈ B → y ∈ B → x' ∈ B → y' ∈ B →
    x ≠ y → x' ≠ y' →
    ∃ g : G,
      Set.image (g : Equiv.Perm Ω) B = B ∧
      (g : Equiv.Perm Ω) x = x' ∧
      (g : Equiv.Perm Ω) y = y'

private def minimumTwoBlockLocalAction
    (G : PermutationGroup) (P : Finset (Set Ω)) : Prop :=
  ∀ B ∈ P,
    locallyPrimitive G B ∧ locallyTwoTransitive G B

private def conjugateSubgroupsBy
    (σ : Equiv.Perm Ω) (R T : PermutationGroup) : Prop :=
  ∀ ρ : Equiv.Perm Ω,
    ρ ∈ T ↔ σ.symm * ρ * σ ∈ R

/-- Claim 37318: a transitive degree-72 permutation group containing regular
copies of `C₂³ × C₃²`, with a minimum nontrivial two-block system of degree
36 and 2-transitive primitive local action, conjugates the two copies inside
the binary 2-closure of their generated group. -/
def claim37318 : Prop :=
  ∀ (R T : PermutationGroup),
    regularCopy R → regularCopy T →
    let G := generatedGroup R T
    transitive G →
    ∀ P : Finset (Set Ω),
      twoBlockMinimum G P →
      minimumTwoBlockLocalAction G P →
      ∃ σ : Equiv.Perm Ω,
        MathlibPlus.GroupTheory.TwoClosure.inTwoClosure G σ ∧
        conjugateSubgroupsBy σ R T

end MathlibPlus.Open.ResearchFormalization.R1451.Degree36BabaiConjugacyClaim37318
