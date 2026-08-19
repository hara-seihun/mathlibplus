import MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On every finite uniform Boolean cube, intrinsic cumulative posterior-variance
area is chord-convex between any two Boolean functions of deterministic
decision-tree depth at most two.
-/
def twoComponentDepthTwoIntrinsicAreaChord : Prop :=
  ∀ n : ℕ, n = 0 ∨
    DepthTwoOracleAreaSchema.twoComponentIntrinsicAreaChord n

end

end MathlibPlus.Open.Probability
