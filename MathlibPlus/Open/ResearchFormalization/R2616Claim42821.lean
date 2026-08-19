import MathlibPlus.Open.Analysis.DyadicMobiusEnergy

namespace MathlibPlus.Open.ResearchFormalization.R2616Claim42821

noncomputable section

open MathlibPlus.Open.Analysis

/-- The exact summand in the full Möbius Laplace series. -/
def fullSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n then
    (ArithmeticFunction.moebius n : ℝ) * Real.exp (-((n : ℝ) * x))
  else 0

/-- The exact summand in the odd-part Möbius Laplace series. -/
def oddSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 1 then
    (ArithmeticFunction.moebius n : ℝ) * Real.exp (-((n : ℝ) * x))
  else 0

/-- The named series are the canonical full and odd Möbius transforms. -/
def F (x : ℝ) : ℝ := fullMobiusTransform x
def A (x : ℝ) : ℝ := oddMobiusTransform x

/-- Claim 42821: for every positive input, the full and odd Möbius Laplace
series converge absolutely. -/
def claim42821 : Prop :=
  ∀ x : ℝ, 0 < x →
    Summable (fun n : ℕ => ‖fullSeriesTerm x n‖) ∧
      Summable (fun n : ℕ => ‖oddSeriesTerm x n‖)

end

end MathlibPlus.Open.ResearchFormalization.R2616Claim42821
