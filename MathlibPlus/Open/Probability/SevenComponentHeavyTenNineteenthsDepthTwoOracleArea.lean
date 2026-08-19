import MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

namespace MathlibPlus.Open.Probability

noncomputable section

/--
Every convex mixture of seven Boolean functions computed by decision trees of
worst-case depth at most two on a finite uniform Rademacher cube has an
adaptive fresh-coordinate reveal policy with cumulative posterior-variance
area at most two, provided some displayed component has weight at least ten
nineteenths. The prior variance is included. The zero-dimensional cube is
discharged separately by the first disjunct.
-/
def sevenComponentHeavyTenNineteenthsDepthTwoOracleArea : Prop :=
  ∀ n : ℕ, n = 0 ∨
    DepthTwoOracleAreaSchema.heavyMixtureAreaAtMost 7 n (10 / 19 : ℝ)

end

end MathlibPlus.Open.Probability
