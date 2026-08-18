import MathlibPlus.Open.Analysis.DepthNormIdentityK0125

open Filter

namespace MathlibPlus.Open.Analysis.DepthNormIdentityK0125

noncomputable section

def macroscopicLambertDepthAction_8892 : Prop :=
  (∀ (m N : ℕ), 0 < m → m < N →
      (compactLambertWNat N - compactLambertWNat m) +
          Real.log (compactLambertWNat N / compactLambertWNat m) =
        Real.log ((N : ℝ) / (m : ℝ))) ∧
    (∀ (m N : ℕ → ℕ) (τ : ℝ),
      (∀ k, m k < N k) →
        Filter.Tendsto (fun k : ℕ => (N k : ℝ)) atTop atTop →
          Filter.Tendsto
              (fun k : ℕ => (m k : ℝ) / (N k : ℝ)) atTop (nhds τ) →
            0 ≤ τ →
              τ ≤ 1 →
                Filter.Tendsto
                  (fun k : ℕ =>
                    trailingLambertAction (m k) (N k) / (N k : ℝ))
                  atTop (nhds (macroscopicAction τ))) ∧
    (∀ (m N : ℕ → ℕ) (τ : ℝ),
      (∀ k, m k < N k) →
        Filter.Tendsto (fun k : ℕ => (N k : ℝ)) atTop atTop →
          Filter.Tendsto
              (fun k : ℕ => (m k : ℝ) / (N k : ℝ)) atTop (nhds τ) →
            0 < τ →
              τ ≤ 1 →
                Filter.Tendsto
                  (fun k : ℕ =>
                    compactLambertWNat (N k) - compactLambertWNat (m k))
                  atTop (nhds (-Real.log τ))) ∧
    (∀ τ : ℝ, 0 < τ → τ < 1 →
      HasDerivAt macroscopicAction (Real.log τ) τ) ∧
    macroscopicAction 0 = 1 ∧
    (∀ τ : ℝ, 0 ≤ τ → τ < 1 → 0 < macroscopicAction τ) ∧
    macroscopicAction 1 = 0

end

end MathlibPlus.Open.Analysis.DepthNormIdentityK0125
