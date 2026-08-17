import Mathlib
import MathlibPlus.Open.Research.R1184Claim41746

namespace MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

noncomputable section

open MathlibPlus.Open.Research.R1184Formalization_41746

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

/-- Cumulative block sizes are obtained from the displayed successive ratios,
starting with the singleton block size. -/
def cumulativeBlockSizes (schedule : List ℕ) : List ℕ :=
  List.scanl (fun accumulated degree => accumulated * degree) 1 schedule

def exceptionalScheduleA : List ℕ := [2, 3, 2, 2]
def exceptionalScheduleB : List ℕ := [2, 4, 3]
def exceptionalScheduleC : List ℕ := [4, 3, 2]

def exceptionalDegree24Schedule (schedule : List ℕ) : Prop :=
  schedule = exceptionalScheduleA ∨
    schedule = exceptionalScheduleB ∨
      schedule = exceptionalScheduleC

/-- The exact schedule arithmetic, including the fact that all three terminal
chains omit cumulative size three. -/
def exceptionalScheduleArithmetic : Prop :=
  cumulativeBlockSizes exceptionalScheduleA = [1, 2, 6, 12, 24] ∧
    cumulativeBlockSizes exceptionalScheduleB = [1, 2, 8, 24] ∧
      cumulativeBlockSizes exceptionalScheduleC = [1, 4, 12, 24] ∧
        3 ∉ cumulativeBlockSizes exceptionalScheduleA ∧
          3 ∉ cumulativeBlockSizes exceptionalScheduleB ∧
            3 ∉ cumulativeBlockSizes exceptionalScheduleC

/-- A recursive exceptional terminal is attached to the actual odd-Hall
prefix scale `n`, rather than treated as an unrelated degree-24 group.  The
prefix cumulative sizes are divisors of `n`; the terminal schedule is one of
the three cited exceptional schedules. -/
def exceptionalTerminalBranch
    (m n : ℕ) (pre terminal : List ℕ) : Prop :=
  m = 3 * n ∧
    0 < n ∧
      (cumulativeBlockSizes pre).getLast? = some n ∧
        (∀ q ∈ cumulativeBlockSizes pre, q ∣ n) ∧
          exceptionalDegree24Schedule terminal

/-- Exact full-carrier block-chain interface for the cited limitation.  It
quantifies over regular copies of `E(C_m,8)` and over the generated-group
conjugator from the normal block-chain theorem, but makes no existential claim
that an exceptional terminal or a counterexample group exists. -/
def exceptionalHallJoinNonForcingInterface
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] : Prop :=
  ∀ (m n : ℕ) (R T : Subgroup (Perm Ω)),
    1 < m →
      Odd m →
        Squarefree m →
          regularECopy m R →
              regularECopy m T →
                ∀ g : generatedPair R T,
                  ∀ (pre terminal : List ℕ)
                    (chain : List (Set (Set Ω))),
                    exceptionalTerminalBranch m n pre terminal →
                      normalBlockSchedule
                          (generatedPair R
                            (conjugateSubgroup (g : Perm Ω) T))
                          (pre ++ terminal) chain →
                        (∀ q ∈ cumulativeBlockSizes (pre ++ terminal),
                          q ≠ m) ∧
                          ¬ chainContainsBlockSize m chain

/-- Claim 41749: the three recursive degree-24 exceptional schedules have the
listed cumulative block sizes and skipped size three; with the actual regular
`E(C_m,8)` pair, generated-group conjugation, and normal block-chain/Hall-block
interface in place, the exceptional schedule is a non-forcing branch rather
than an asserted existence of unrelated counterexample groups. -/
def claim41749 : Prop :=
  exceptionalScheduleArithmetic ∧
    (∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
      exceptionalHallJoinNonForcingInterface (Ω := Ω))

end

end MathlibPlus.Open.ResearchFormalization.R1184.Claim41749
