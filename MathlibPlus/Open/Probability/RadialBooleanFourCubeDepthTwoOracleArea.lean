import MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On the uniform four-sign cube, every scalar multiple of a Boolean table that
lies in the convex hull of deterministic depth-at-most-two Boolean tables has
a fresh adaptive coordinate policy with root-inclusive cumulative
posterior-variance area at most two.
-/
def radialBooleanFourCubeDepthTwoOracleArea : Prop :=
  DepthTwoOracleAreaSchema.radialBooleanAreaAtMost 4

end

end MathlibPlus.Open.Probability
