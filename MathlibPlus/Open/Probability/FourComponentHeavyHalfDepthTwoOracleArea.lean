import MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

namespace MathlibPlus.Open.Probability

noncomputable section

/--
Every convex mixture of four Boolean functions computed by decision trees of
worst-case depth at most two on a finite uniform Rademacher cube has an
adaptive fresh-coordinate reveal policy with cumulative posterior-variance
area at most two, provided some displayed component has weight at least one
half. The prior variance is included. The zero-dimensional cube is discharged
separately by the first disjunct.
-/
def fourComponentHeavyHalfDepthTwoOracleArea : Prop :=
  ∀ n : ℕ, n = 0 ∨
    DepthTwoOracleAreaSchema.heavyMixtureAreaAtMost 4 n (1 / 2 : ℝ)

end

end MathlibPlus.Open.Probability
