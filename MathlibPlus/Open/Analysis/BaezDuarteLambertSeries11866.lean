import MathlibPlus.Open.Analysis.BaezDuarteErrorGeneratingFunction11867

namespace MathlibPlus.Open.Analysis.BaezDuarteLambertSeries11866

noncomputable section

/-- Claim 11866: the divisor-polynomial Lambert identity on the reviewed
complex common-convergence domain. -/
def claim11866 : Prop :=
  ∀ (u : ℝ) (z : ℂ),
    MathlibPlus.Open.Analysis.BaezDuarteErrorGeneratingFunction11867.commonConvergenceDomain
      u z →
      MathlibPlus.Open.Analysis.BaezDuarteErrorGeneratingFunction11867.divisorGeneratingFunction
          (Real.exp (-u)) z =
        ∑' n : ℕ+,
          ((ArithmeticFunction.moebius (n : ℕ) : ℝ) : ℂ) *
              (Real.exp (-u) : ℂ) ^ (n : ℕ) * z ^ (n : ℕ) /
            (1 - z ^ (n : ℕ))

end

end MathlibPlus.Open.Analysis.BaezDuarteLambertSeries11866
