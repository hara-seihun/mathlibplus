import Mathlib
import MathlibPlus.Open.ResearchBatchHallControls

namespace MathlibPlus.Open.Research.R1184Formalization_41746

noncomputable section

open MathlibPlus.Open.ResearchBatchHallControls

abbrev Perm (Ω : Type*) := Equiv.Perm Ω
abbrev Gm := MathlibPlus.Open.ResearchBatchHallControls.Gm

def regularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Perm Ω) x = y

def eTranslationSet (m : ℕ) : Set (Perm (Gm m)) :=
  {e | ∃ g : Gm m, ∀ x : Gm m, e x = gmMul m g x}

def eStandardCopy (m : ℕ) : Subgroup (Perm (Gm m)) :=
  Subgroup.closure (eTranslationSet m)

def regularECopy {Ω : Type*} [Fintype Ω]
    (m : ℕ) (R : Subgroup (Perm Ω)) : Prop :=
  regularPermutationSubgroup R ∧
    Fintype.card Ω = 8 * m ∧
    Nonempty (R ≃* eStandardCopy m)

def generatedPair {Ω : Type*}
    (R T : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure ((R : Set (Perm Ω)) ∪ (T : Set (Perm Ω)))

def conjugationHom {G : Type*} [Group G] (g : G) : G →* G :=
  (MulAut.conj g : G ≃* G).toMonoidHom

def conjugateSubgroup {G : Type*} [Group G]
    (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (conjugationHom g)

def blockFamily {Ω : Type*} (ℬ : Set (Set Ω)) : Prop :=
  (∀ B ∈ ℬ, B.Nonempty) ∧
    (∀ B C, B ∈ ℬ → C ∈ ℬ → B ≠ C → Disjoint B C) ∧
    ⋃₀ ℬ = Set.univ

def preservesBlocks {Ω : Type*}
    (G : Subgroup (Perm Ω)) (ℬ : Set (Set Ω)) : Prop :=
  ∀ g : G, ∀ B : Set Ω, B ∈ ℬ →
    (g : Perm Ω) '' B ∈ ℬ

def normalCommonBlockSystem {Ω : Type*}
    (R T : Subgroup (Perm Ω)) (ℬ : Set (Set Ω)) : Prop :=
  blockFamily ℬ ∧ preservesBlocks (generatedPair R T) ℬ

def blockStabilizer {Ω : Type*}
    (R : Subgroup (Perm Ω)) (B : Set Ω) : Set R :=
  {r | (r : Perm Ω) '' B = B}

def subgroupOrbitInCopy {Ω : Type*}
    (R : Subgroup (Perm Ω)) (H : Subgroup R) (x : Ω) : Set Ω :=
  {y | ∃ h : H, ((h : R) : Perm Ω) x = y}

def orbitPartitionInCopy {Ω : Type*}
    (R : Subgroup (Perm Ω)) (H : Subgroup R) : Set (Set Ω) :=
  {B | ∃ x : Ω, subgroupOrbitInCopy R H x = B}

def oddHallData {Ω : Type*} [Fintype Ω]
    (m : ℕ) (R : Subgroup (Perm Ω)) (H : Subgroup R) : Prop :=
  Nat.card H = m ∧
    (∀ Q : Subgroup R, Nat.card Q = m → Q = H) ∧
    (∀ Q : Subgroup R, Odd (Nat.card Q) → Q ≤ H) ∧
    (∀ φ : R ≃* R, H.map φ.toMonoidHom = H)

def commonOddHallConclusion {Ω : Type*} [Fintype Ω]
    (m : ℕ) (R T : Subgroup (Perm Ω)) : Prop :=
  ∃ g : generatedPair R T,
    let Tg := conjugateSubgroup (g : Perm Ω) T
    ∃ HR : Subgroup R, ∃ HT : Subgroup Tg,
      oddHallData m R HR ∧
      oddHallData m Tg HT ∧
      orbitPartitionInCopy R HR = orbitPartitionInCopy Tg HT ∧
      normalCommonBlockSystem R Tg (orbitPartitionInCopy R HR) ∧
      Set.ncard (orbitPartitionInCopy R HR) = 8 ∧
      (∀ B : Set Ω, B ∈ orbitPartitionInCopy R HR → B.ncard = m)

def blockRefinementByRatio {Ω : Type*} [Fintype Ω]
    (P Q : Set (Set Ω)) (q : ℕ) : Prop :=
  blockFamily P ∧ blockFamily Q ∧
    (∀ B : Set Ω, B ∈ P → ∃! C : Set Ω, C ∈ Q ∧ B ⊆ C) ∧
    (∀ C : Set Ω, C ∈ Q →
      Set.ncard {B : Set Ω | B ∈ P ∧ B ⊆ C} = q)

def singletonPartition {Ω : Type*} : Set (Set Ω) :=
  {B | ∃ x : Ω, B = ({x} : Set Ω)}

def universalPartition {Ω : Type*} : Set (Set Ω) :=
  {B | B = Set.univ}

def normalBlockSchedule {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Perm Ω)) (schedule : List ℕ)
    (chain : List (Set (Set Ω))) : Prop :=
  chain.length = schedule.length + 1 ∧
    chain.head? = some singletonPartition ∧
    chain.getLast? = some universalPartition ∧
    (∀ i : ℕ, ∀ hi : i < chain.length,
      preservesBlocks G (chain.get ⟨i, hi⟩)) ∧
    (∀ i : ℕ, ∀ hi : i < schedule.length,
      ∃ hnext : i + 1 < chain.length,
        blockRefinementByRatio
          (chain.get ⟨i, by omega⟩)
          (chain.get ⟨i + 1, hnext⟩)
          (schedule.get ⟨i, hi⟩))

def chainContainsBlockSize {Ω : Type*}
    (m : ℕ) (chain : List (Set (Set Ω))) : Prop :=
  ∃ P ∈ chain, ∃ B : Set Ω, B ∈ P ∧ B.ncard = m

def blockChainForcesHallJoin (schedule : List ℕ) (m : ℕ) : Prop :=
  ∀ (G : Subgroup (Perm (Fin 24)))
    (chain : List (Set (Set (Fin 24)))),
    normalBlockSchedule G schedule chain →
      chainContainsBlockSize m chain

def normalPrimeBlockBranch {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Perm Ω)) : Prop :=
  ∃ schedule : List ℕ,
    ∃ chain : List (Set (Set Ω)),
      ∃ i : Fin schedule.length,
        normalBlockSchedule G schedule chain ∧
          schedule.get i = 3 ∧
          ∀ j : Fin schedule.length, j.val < i.val →
            schedule.get j ≠ 2

def exceptionalScheduleCounterexample (schedule : List ℕ) (m : ℕ) : Prop :=
  ∃ G : Subgroup (Perm (Fin 24)),
    ∃ chain : List (Set (Set (Fin 24))),
      (∀ x y : Fin 24, ∃ g : G, (g : Perm (Fin 24)) x = y) ∧
      normalBlockSchedule G schedule chain ∧
      ¬ chainContainsBlockSize m chain

def cumulativeBlockSizes : List ℕ → List ℕ
  | [] => [1]
  | q :: qs => 1 :: (cumulativeBlockSizes qs).map (q * ·)

def exceptionalScheduleA : List ℕ := [2, 3, 2, 2]
def exceptionalScheduleB : List ℕ := [2, 4, 3]
def exceptionalScheduleC : List ℕ := [4, 3, 2]

/-- Claim 41746. -/
def claim41746 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω],
      Fintype.card Ω = 8 * m →
      ∀ R T : Subgroup (Perm Ω),
        regularECopy m R → regularECopy m T →
        ∀ ℬ : Set (Set Ω),
          normalCommonBlockSystem R T ℬ →
          (∀ B : Set Ω, B ∈ ℬ → B.ncard = m) →
          ∃ HR : Subgroup R, ∃ HT : Subgroup T,
            oddHallData m R HR ∧
            oddHallData m T HT ∧
            (∀ B : Set Ω, B ∈ ℬ →
              Nat.card {r : R // r ∈ blockStabilizer R B} = m ∧
                blockStabilizer R B = (HR : Set R)) ∧
            (∀ B : Set Ω, B ∈ ℬ →
              Nat.card {t : T // t ∈ blockStabilizer T B} = m ∧
                blockStabilizer T B = (HT : Set T)) ∧
            ℬ = orbitPartitionInCopy R HR ∧
            ℬ = orbitPartitionInCopy T HT


end

end MathlibPlus.Open.Research.R1184Formalization_41746
