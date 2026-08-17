import MathlibPlus.Open.Research.R1184Claim41746

namespace MathlibPlus.Open.ResearchFormalization.R1184RegularBlock

noncomputable section

open MathlibPlus.Open.Research.R1184Formalization_41746

/-- Claim 31979: in a regular `E(C_m,8)` copy, every common normal
m-block has the unique odd-Hall subgroup as stabilizer and is its orbit
partition, simultaneously for both copies. -/
def claim31979_regularMBlockOddHall : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω],
      Fintype.card Ω = 8 * m →
      ∀ R T : Subgroup (Equiv.Perm Ω),
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

end MathlibPlus.Open.ResearchFormalization.R1184RegularBlock
