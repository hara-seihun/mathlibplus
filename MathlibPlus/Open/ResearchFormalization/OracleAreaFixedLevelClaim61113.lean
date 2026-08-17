import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaFixedLevelClaim61113

noncomputable section

def diagonalLaw : Bool × Bool → ℚ
  | (false, false) => 1 / 2
  | (true, true) => 1 / 2
  | _ => 0

def antidiagonalLaw : Bool × Bool → ℚ
  | (false, true) => 1 / 2
  | (true, false) => 1 / 2
  | _ => 0

def totalMass (μ : Bool × Bool → ℚ) : ℚ :=
  ∑ z, μ z

def firstYes (μ : Bool × Bool → ℚ) : ℚ :=
  ∑ z, if z.1 then μ z else 0

def secondYes (μ : Bool × Bool → ℚ) : ℚ :=
  ∑ z, if z.2 then μ z else 0

def bothYes (μ : Bool × Bool → ℚ) : ℚ :=
  μ (true, true)

def probabilityLaw (μ : Bool × Bool → ℚ) : Prop :=
  (∀ z, 0 ≤ μ z) ∧ totalMass μ = 1

/-- Claim 61113: dependent joint laws with identical one-coordinate yes
marginals can have different all-yes probabilities, so marginal-only
reconstruction is impossible. -/
def claim61113 : Prop :=
  probabilityLaw diagonalLaw ∧
    probabilityLaw antidiagonalLaw ∧
    (∀ z, 0 ≤ diagonalLaw z) ∧
    (∀ z, 0 ≤ antidiagonalLaw z) ∧
    firstYes diagonalLaw = 1 / 2 ∧
    firstYes antidiagonalLaw = 1 / 2 ∧
    secondYes diagonalLaw = 1 / 2 ∧
    secondYes antidiagonalLaw = 1 / 2 ∧
    bothYes diagonalLaw = 1 / 2 ∧
    bothYes antidiagonalLaw = 0 ∧
    (∀ A : ℚ → ℚ → ℚ,
      ¬ (A (firstYes diagonalLaw) (secondYes diagonalLaw) =
          bothYes diagonalLaw ∧
        A (firstYes antidiagonalLaw) (secondYes antidiagonalLaw) =
          bothYes antidiagonalLaw))

end
end MathlibPlus.Open.ResearchFormalization.OracleAreaFixedLevelClaim61113
