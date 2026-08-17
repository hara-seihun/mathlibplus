import MathlibPlus.Open.Analysis.ExplicitSecondCumulantTailBound13428

open Filter

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0085

noncomputable section

open MathlibPlus.Open.Analysis.Claim13420
open MathlibPlus.Open.Analysis.ExplicitSecondCumulant13428

/-- Claim 13427: the exact finite renormalized products are
`A_y * exp(P_y)`, while their analytic second-cumulant logarithm branches
converge uniformly on every full half-plane `Re(z) >= sigma₀` to the
holomorphic, nonvanishing limit carrier. -/
def claim13427 : Prop :=
  ∀ (σ₀ : ℝ), (1 / 2 : ℝ) < σ₀ →
    (∀ (y : ℕ) (z : ℂ),
      renormalizedFiniteEulerProduct y z =
        MathlibPlus.Analysis.Claim13408.finiteEulerProduct y z *
          Complex.exp (primeSum y z)) ∧
      TendstoUniformlyOn
        (fun y : ℕ => renormalizedFiniteLogBranch y)
        renormalizedLimitLogBranch (atTop : Filter ℕ)
        {z : ℂ | σ₀ ≤ z.re} ∧
      AnalyticOnNhd ℂ renormalizedLimit
        {z : ℂ | σ₀ ≤ z.re} ∧
      (∀ z : ℂ, σ₀ ≤ z.re → renormalizedLimit z ≠ 0)

end
end MathlibPlus.Open.Analysis.FormalizationBatchO0085
