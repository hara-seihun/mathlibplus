import MathlibPlus.Open.Analysis.StieltjesContext

namespace MathlibPlus.Open.Analysis

def differentiatedStieltjesLaurentSeries : Prop :=
  stieltjesContext ∧
    (∀ t : ℝ, 0 < t →
      stieltjesZ t =
        ∑' n : {n : ℕ // 1 ≤ n},
          ((-1 : ℝ) ^ n.1) * stieltjesConstants n.1 *
              t ^ (n.1 - 1) /
            (Nat.factorial (n.1 - 1) : ℝ)) ∧
    Filter.Tendsto stieltjesZ (nhdsWithin 0 (Set.Ioi 0)) (nhds stieltjesAlpha)

end MathlibPlus.Open.Analysis
