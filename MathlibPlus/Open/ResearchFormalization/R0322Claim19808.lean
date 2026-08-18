import MathlibPlus.Open.ResearchFormalization.R0322Claim19813

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19808

open scoped BigOperators Classical

noncomputable section

/-- The admitted closed form for the power-sum image under the supplied
specialization map. -/
def closedFormPowerSum_claim19808 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    MathlibPlus.Open.ResearchFormalization.R0322Claim19813.γ
        (MathlibPlus.Open.ResearchFormalization.R0322Claim19813.p m) =
      MathlibPlus.Open.ResearchFormalization.R0322Claim19813.y *
          MathlibPlus.Open.ResearchFormalization.R0322Claim19813.x ^ m *
          (MathlibPlus.Open.ResearchFormalization.R0322Claim19813.y -
            MathlibPlus.Open.ResearchFormalization.R0322Claim19813.z) ^ (m - 1) +
        MathlibPlus.Open.ResearchFormalization.R0322Claim19813.y *
          (MathlibPlus.Open.ResearchFormalization.R0322Claim19813.y - 1) ^ (m - 1)

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19808
