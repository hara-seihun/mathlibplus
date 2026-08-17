import MathlibPlus.Open.Combinatorics.Claim5457

namespace MathlibPlus.Open.Combinatorics.Claim5452

noncomputable section

/-- The reversal-fixed rational rooted-vertex module of `P_k` has the
claimed ceiling-half dimension. -/
def rootedPathOrbitSpaceDimension_claim5452 : Prop :=
  ∀ k : ℕ,
    Module.finrank ℚ
      (MathlibPlus.Open.Combinatorics.Claim5457.pathOrbitSpace k) =
      MathlibPlus.Open.Combinatorics.Claim5457.ceilHalf k

end

end MathlibPlus.Open.Combinatorics.Claim5452
