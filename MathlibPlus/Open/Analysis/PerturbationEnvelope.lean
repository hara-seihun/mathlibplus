import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim59782

/-- The perturbed terminal expression. -/
def terminalExpression (δt δy : ℝ) : ℝ :=
  1579 / 10000 + δt + (1 / 2) * (1 / 10 + δy) ^ 2

/-- The exact sharp envelope claimed for nonnegative budgets. -/
def sharpEnvelope (εt εy : ℝ) : ℝ :=
  1629 / 10000 + εt + εy / 10 + εy ^ 2 / 2

/-- Exact sharpness, the consequence for Λ, and the stated endpoint attainment. -/
def sharpPerturbationEnvelope : Prop :=
  ∀ εt εy : ℝ, 0 ≤ εt → 0 ≤ εy →
    let E := sharpEnvelope εt εy
    let values : Set ℝ :=
      {v | ∃ δt δy : ℝ,
        |δt| ≤ εt ∧ |δy| ≤ εy ∧ v = terminalExpression δt δy}
    IsGreatest values E ∧
      (∀ Λ δt δy : ℝ,
        |δt| ≤ εt → |δy| ≤ εy →
          Λ ≤ terminalExpression δt δy → Λ ≤ E) ∧
      terminalExpression εt εy = E ∧
      (∃ Λ : ℝ, Λ = terminalExpression εt εy ∧ Λ = E)

end MathlibPlus.Open.Analysis.Claim59782
