import MathlibPlus.Open.Analysis.CyclicDivisor

namespace MathlibPlus.Open.Analysis.CyclicDirichletClaim10013

noncomputable section

/-- A cyclic Dirichlet logarithmic derivative has the corresponding global
imaginary period after its meromorphic continuation. -/
def claim10013 : Prop :=
  ∀ (m : ℕ) (R : ℂ → ℂ) (β : ℕ → ℂ) (σ : ℝ),
    1 < m →
      1 / 2 < σ →
        (MeromorphicOn R Set.univ ∧
          (∀ s : ℂ, σ < s.re → R s ≠ 0) ∧
          (∀ s : ℂ, σ < s.re →
            -deriv R s / R s =
              ∑' k : {k : ℕ // 0 < k},
                β k.1 *
                  Complex.exp
                    (-((k.1 : ℂ) * s) *
                      Complex.ofReal (Real.log (m : ℝ)))) ∧
          (∀ s : ℂ, σ < s.re →
            Summable (fun k : {k : ℕ // 0 < k} =>
              ‖β k.1 *
                Complex.exp
                  (-((k.1 : ℂ) * s) *
                    Complex.ofReal (Real.log (m : ℝ)))‖))) →
        ∃ C : ℂ, ∃ G : ℂ → ℂ,
          C ≠ 0 ∧
            AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) 1) ∧
            (∀ s : ℂ, σ < s.re →
              ‖cyclicCoordinate (m : ℝ) s‖ < 1 ∧
                R s = C * Complex.exp (G (cyclicCoordinate (m : ℝ) s))) ∧
            (∀ s : ℂ,
              R (s +
                  (((2 * Real.pi / Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)) =
                R s)

end

end MathlibPlus.Open.Analysis.CyclicDirichletClaim10013
