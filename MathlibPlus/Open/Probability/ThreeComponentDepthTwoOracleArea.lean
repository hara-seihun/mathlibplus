import MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

namespace MathlibPlus.Open.Probability

noncomputable section

/--
Every convex mixture of three Boolean functions computed by decision trees of
worst-case depth at most two on a finite uniform Rademacher cube has an
adaptive fresh-coordinate reveal policy with cumulative posterior-variance
area at most two. The prior variance is included. The zero-dimensional cube
is discharged separately by the first disjunct.
-/
def threeComponentDepthTwoOracleArea : Prop :=
  ∀ n : ℕ, n = 0 ∨ DepthTwoOracleAreaSchema.mixtureAreaAtMost 3 n

end

end MathlibPlus.Open.Probability
