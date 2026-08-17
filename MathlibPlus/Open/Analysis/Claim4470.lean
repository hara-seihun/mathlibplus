import MathlibPlus.Open.ResearchFormalizationBatch_01a001ac_7d55_7d4a_8f44_f4a292b299c9

namespace MathlibPlus.Open.Analysis.Claim4470

/-- Scaling the finite-place sequence by a real scalar scales every finite
channel by that scalar. -/
def channelHomogeneity_claim4470 : Prop :=
  ∀ (support : Finset ℕ) (sequence : ℕ → ℝ) (c : ℝ) (r : ℕ) (x : ℝ),
    MathlibPlus.Open.ResearchFormalizationBatch.finiteChannel
        support (fun n => c * sequence n) r x =
      c * MathlibPlus.Open.ResearchFormalizationBatch.finiteChannel
        support sequence r x

end MathlibPlus.Open.Analysis.Claim4470
