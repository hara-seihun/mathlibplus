import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- The all-order negative-Loewner criterion for the logarithmic derivative of the
centered completed Riemann xi function.  The second conjunct records the stated
finite-principal-minor falsifier consequence. -/
def allOrderCompletedZetaLoewnerCriterion : Prop :=
  let completedXi : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s
  let centeredXi : ℂ → ℂ := fun z => completedXi ((1 / 2 : ℂ) + z)
  let H : ℝ → ℝ := fun x =>
    ((deriv centeredXi (Real.sqrt x)) / centeredXi (Real.sqrt x)).re / Real.sqrt x
  let negativeLoewner : (n : ℕ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun _ x i j =>
      if x i = x j then -deriv H (x i)
      else -(H (x i) - H (x j)) / (x i - x j)
  ((∀ (n : ℕ) (x : Fin n → ℝ),
      (∀ i, (1 : ℝ) / 4 < x i) → (negativeLoewner n x).PosSemidef) ↔
      RiemannHypothesis) ∧
    ∀ (n : ℕ) (x : Fin n → ℝ),
      (∀ i, (1 : ℝ) / 4 < x i) →
      (negativeLoewner n x).det < 0 → ¬RiemannHypothesis

end MathlibPlus.Open.AnalyticNumberTheory
