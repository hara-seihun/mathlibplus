import Mathlib
import MathlibPlus.Open.AnalyticNumberTheory.O0339CompletedShiftClaims
import MathlibPlus.Open.ResearchFormalization.Batch

namespace MathlibPlus.Open.AnalyticNumberTheory.O0339CompletedShiftClaims

noncomputable section

open Filter
open MathlibPlus.Open.ResearchFormalization.Batch

/-- An absolutely convergent ordinary Dirichlet series with arbitrary complex
coefficients on the positive-integer carrier. -/
def ordinaryDirichletSeries15338 (F : ℂ → ℂ) : Prop :=
  ∃ (a : ℕ+ → ℂ) (σ₀ : ℝ),
    (∀ s : ℂ, σ₀ < s.re →
      Summable (fun n : ℕ+ => ‖dirichletTerm a n s‖)) ∧
    (∀ s : ℂ, σ₀ < s.re →
      F s = ∑' n : ℕ+, dirichletTerm a n s)

/-- Claim 15538: the canonical exponential of every nonzero real compact
completed shift is excluded from absolutely convergent ordinary Dirichlet
series, including series with signed or complex coefficients. -/
def claim15538 : Prop :=
  ∀ (T : ComplexDistribution) (A : ℝ) (Y : ℂ → ℂ),
    T ≠ 0 →
      compactSupportIn T A →
        isRealDistribution T →
          completedShiftDefinition T A Y →
            ¬ ordinaryDirichletSeries15338
                (fun s : ℂ => Complex.exp (Y s))

end

end MathlibPlus.Open.AnalyticNumberTheory.O0339CompletedShiftClaims
