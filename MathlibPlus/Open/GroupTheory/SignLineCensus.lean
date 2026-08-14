import Mathlib

namespace MathlibPlus.Open.GroupTheory.SignLineCensus

noncomputable section

abbrev Base28 := ZMod 28
abbrev Ternary := ZMod 3

def signLine (ε : Base28 → Ternary) : Prop :=
  ε 0 = 1 ∧ ∀ b, ε b = 1 ∨ ε b = -1

def hasPeriod (ε : Base28 → Ternary) (k : Base28) : Prop :=
  ∀ b, ε (b + k) = ε b

def periodicSignLine (ε : Base28 → Ternary) : Prop :=
  ∃ k, k ≠ 0 ∧ hasPeriod ε k

def hasPeriodSubgroupOrder (ε : Base28 → Ternary) (n : ℕ) : Prop :=
  ∃ P : AddSubgroup Base28,
    Nat.card P = n ∧ ∀ k, k ∈ P ↔ hasPeriod ε k

/-- Claim 37036: exact normalized sign-line and periodicity census, including
period-subgroup orders for the unequal periodic lines. -/
def claim37036 : Prop :=
  Set.ncard {ε : Base28 → Ternary | signLine ε} = 2 ^ 27 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ periodicSignLine ε} = 8198 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ ¬periodicSignLine ε ∧ ε ≠ (fun _ => 1)} = 134209530 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ periodicSignLine ε ∧ ε ≠ (fun _ => 1)} = 8197 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ ε ≠ (fun _ => 1) ∧ hasPeriodSubgroupOrder ε 2} = 8127 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ ε ≠ (fun _ => 1) ∧ hasPeriodSubgroupOrder ε 4} = 63 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ ε ≠ (fun _ => 1) ∧ hasPeriodSubgroupOrder ε 7} = 6 ∧
    Set.ncard {ε : Base28 → Ternary |
      signLine ε ∧ ε ≠ (fun _ => 1) ∧ hasPeriodSubgroupOrder ε 14} = 1

end
end MathlibPlus.Open.GroupTheory.SignLineCensus
