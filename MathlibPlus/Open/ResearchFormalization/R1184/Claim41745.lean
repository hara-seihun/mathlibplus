import MathlibPlus.Open.Research.R1184Claim41746

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1184.Claim41745

noncomputable section

open MathlibPlus.Open.Research.R1184Formalization_41746

private def oddPrimeFactorsDescending (m : ℕ) : List ℕ :=
  (Nat.primeFactors m).sort (fun a b => b ≤ a)

private def primeFactorSchedule (m : ℕ) : List ℕ :=
  oddPrimeFactorsDescending m ++ [2, 2, 2]

private def cumulativeBlockSizes : List ℕ → List ℕ
  | [] => [1]
  | q :: qs => 1 :: (cumulativeBlockSizes qs).map (q * ·)

private def primeScheduleData (m : ℕ) : Prop :=
  (∀ q ∈ oddPrimeFactorsDescending m, Nat.Prime q ∧ Odd q) ∧
    List.prod (oddPrimeFactorsDescending m) = m ∧
    List.Pairwise (· ≥ ·) (primeFactorSchedule m)

/-- Claim 41745: in the nonexceptional normal block chain for a regular
`E(C_m,8)` pair, the distinct odd prime factors occur before the three
2-factors and the intermediate chain contains blocks of size `m`. -/
def nonincreasingBlockChainContainsM_claim41745 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m → ¬ 3 ∣ m →
    ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω],
      Fintype.card Ω = 8 * m →
      ∀ R T : Subgroup (Perm Ω),
        regularECopy m R → regularECopy m T →
        ∃ g : generatedPair R T,
          ∃ chain : List (Set (Set Ω)),
            primeScheduleData m ∧
              normalBlockSchedule
                (generatedPair R (conjugateSubgroup (g : Perm Ω) T))
                (primeFactorSchedule m) chain ∧
              m ∈ cumulativeBlockSizes (primeFactorSchedule m) ∧
              chainContainsBlockSize m chain

end

end MathlibPlus.Open.ResearchFormalization.R1184.Claim41745
