import MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

namespace MathlibPlus.Open.Probability

noncomputable section

/--
For every positive finite number of displayed components, a convex mixture of
Boolean functions computed by deterministic decision trees of worst-case depth
at most two on a finite uniform Boolean cube has an adaptive fresh-coordinate
policy of root-inclusive cumulative posterior-variance area at most two when
one displayed component has weight at least `2 / 3`. Zero weights and repeated
semantic functions are allowed; the zero-dimensional cube is discharged by a
separate trivial disjunct.
-/
def arbitraryComponentCountTwoThirdsHeavyDepthTwoOracleArea : Prop :=
  ∀ m : ℕ, 0 < m →
    ∀ n : ℕ, n = 0 ∨
      DepthTwoOracleAreaSchema.heavyMixtureAreaAtMost m n ((2 : ℝ) / 3)

end

end MathlibPlus.Open.Probability
