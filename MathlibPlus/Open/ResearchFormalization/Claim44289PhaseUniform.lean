import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim44289

/-- The phase-uniform coefficient identities and their absolute-value bound. -/
def phaseUniformCoefficientIdentity_claim44289 : Prop :=
  ∀ (a A B : ℝ),
    0 ≤ a →
      let F : ℝ := B - a * A
      let G : ℝ := A - a * B
      B - A = (F - G) / (1 + a) ∧
        ((1 - a) / (1 + a)) * (B + A) =
          (F + G) / (1 + a) ∧
        max (|B - A|)
            (((1 - a) / (1 + a)) * |B + A|) ≤
          (|F| + |G|) / (1 + a)

end MathlibPlus.Open.ResearchFormalization.Claim44289
