import MathlibPlus.Open.ResearchFormalization.Q0132Claim16821

namespace MathlibPlus.Open.ResearchFormalization.Q0132Claim16824

open MathlibPlus.Open.ResearchFormalization.Q0132Claim16821

noncomputable section

/-- Claim 16824: every strictly-larger-than-24 width-two witness has the
strengthened `840u` residual form and the parity-conditioned fifth prime. -/
def strengthenedN840uResidual_claim16824 : Prop :=
  ∀ n : ℕ, 24 < n → widthTwoWitness n →
    ∃ u : ℕ,
      n = 840 * u ∧
        Nat.Prime (140 * u - 1) ∧
        Nat.Prime (210 * u - 1) ∧
        Nat.Prime (420 * u - 1) ∧
        Nat.Prime (840 * u - 1) ∧
        (Even u → Nat.Prime (105 * u - 1)) ∧
        (Odd u → Nat.Prime ((105 * u - 1) / 2))

end

end MathlibPlus.Open.ResearchFormalization.Q0132Claim16824
