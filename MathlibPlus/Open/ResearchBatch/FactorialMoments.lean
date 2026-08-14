import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchBatch

noncomputable section

def factorialLogMomentIntegrand (q : ℕ) (t : ℝ) : ℝ :=
  (Real.log t) ^ q / t ^ 2

/-- Claim 4119: the factorial logarithmic-moment and discrete tail bounds. -/
def claim_4119 : Prop :=
  ∀ q : ℕ,
    (∀ t : ℝ, 1 ≤ t → 0 ≤ factorialLogMomentIntegrand q t) ∧
    MonotoneOn (factorialLogMomentIntegrand q)
      (Set.Icc (1 : ℝ) (Real.exp ((q : ℝ) / 2))) ∧
    AntitoneOn (factorialLogMomentIntegrand q)
      (Set.Ici (Real.exp ((q : ℝ) / 2))) ∧
    (∫ t in Set.Ici (1 : ℝ), factorialLogMomentIntegrand q t) = (q.factorial : ℝ) ∧
    factorialLogMomentIntegrand q (Real.exp ((q : ℝ) / 2)) =
      ((q : ℝ) / 2) ^ q * Real.exp (-(q : ℝ)) ∧
    (∀ t : ℝ, 1 ≤ t →
      factorialLogMomentIntegrand q t ≤
        ((q : ℝ) / 2) ^ q * Real.exp (-(q : ℝ))) ∧
    ((q : ℝ) / 2) ^ q * Real.exp (-(q : ℝ)) ≤ (q.factorial : ℝ) ∧
    (∑' n : ℕ,
      if 2 ≤ n then (Real.log (n : ℝ)) ^ q / (n : ℝ) ^ 2 else 0) ≤
      3 * (q.factorial : ℝ)

end

end MathlibPlus.Open.ResearchBatch
