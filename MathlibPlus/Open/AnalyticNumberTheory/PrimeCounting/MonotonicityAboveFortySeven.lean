import MathlibPlus.AxlerMajorant

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-! Claim 695: the exact derivative certificate for the C-0044 polynomial,
the endpoint margin, and the resulting monotonicity of the complete F. -/

def monotonicityAboveFortySeven : Prop :=
  let η : ℝ := 12167 / 500000
  let Q : ℝ → ℝ := fun L =>
    L ^ 8 + η * L ^ 4 * (L - 3) - 30 * η * L ^ 2 +
      (5286 / 5 : ℝ) * L - 243888 / 5
  let F : ℝ → ℝ := MathlibPlus.AxlerMajorant.factorial720Bound
  (∀ L : ℝ, Real.log 47 ≤ L →
      deriv Q L =
          L * (8 * L ^ 6 - 60 * η) + η * L ^ 3 * (5 * L - 12) +
            (5286 / 5 : ℝ) ∧
        0 < L * (8 * L ^ 6 - 60 * η) + η * L ^ 3 * (5 * L - 12) +
            (5286 / 5 : ℝ)) ∧
    Q (Real.log 47) > 35722561 / 10000 ∧
    StrictMonoOn F (Set.Ici (47 : ℝ))

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
