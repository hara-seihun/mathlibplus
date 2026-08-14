import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The archimedean Gamma factor in the complex variable. -/
def gammaR (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) * Complex.Gamma (s / 2)

/-- A meromorphic point which is not analytic, used to state the pole towers. -/
def researchHasPoleAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  MeromorphicAt f z ∧ ¬ AnalyticAt ℂ f z

/-- A zero at a point where the function is analytic. -/
def researchHasZeroAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  AnalyticAt ℂ f z ∧ f z = 0

/-- The ratio occurring in Claim 12316. -/
def gammaRRatio (s : ℂ) : ℂ := gammaR s / gammaR (s + 1)

/-- Claim 12316: the ratio exposes the odd denominator tower, whereas the
Gamma factor itself has the even pole tower and no odd negative zero tower. -/
def claim12316 : Prop :=
  (∀ n : ℕ,
    researchHasPoleAt gammaR (-(2 * (n : ℂ)))) ∧
  (∀ n : ℕ,
    researchHasPoleAt (fun s : ℂ => gammaR (s + 1))
      (-(2 * (n : ℂ) + 1))) ∧
  (∀ n : ℕ,
    researchHasZeroAt gammaRRatio (-(2 * (n : ℂ) + 1))) ∧
  (∀ n : ℕ,
    ¬ researchHasZeroAt gammaR (-(2 * (n : ℂ) + 1)))

end MathlibPlus.Open.ResearchFormalizationBatch
