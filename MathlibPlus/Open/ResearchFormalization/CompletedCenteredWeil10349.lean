import MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.CompletedCenteredWeil10349

open MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner

/-- Claim 10349: the completed centered Weil quadratic form on the
real-even compactly supported test carrier. -/
def claim10349_completedCenteredWeilForm : Prop :=
  ∀ (φ : ℝ → ℝ),
    realEvenCompactTest φ →
      weilQuadraticForm φ =
        (testH φ (Complex.I / 2)).re +
            (testH φ ((-Complex.I) / 2)).re -
          Real.log Real.pi * testAutocorrelation φ 0 +
          (1 / (2 * Real.pi)) *
            (∫ s : ℝ,
              (testH φ (s : ℂ)).re *
                (Complex.digamma
                  (1 / 4 + Complex.I * (s : ℂ) / 2)).re) -
          2 *
            ∑' n : {n : ℕ // 2 ≤ n},
              (ArithmeticFunction.vonMangoldt n.1 /
                  Real.sqrt (n.1 : ℝ)) *
                testAutocorrelation φ (Real.log (n.1 : ℝ))

end MathlibPlus.Open.ResearchFormalization.CompletedCenteredWeil10349
