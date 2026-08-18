import MathlibPlus.Open.ResearchFormalization.CompletedThetaMonic11882

namespace MathlibPlus.Open.ResearchFormalization.O0182Claim11879

noncomputable section

open MathlibPlus.Open.ResearchFormalization.CompletedTheta11882

/-- Claim 11879: the completed-xi even jet is the source of the literal
checkerboard moment recurrence and signed moments. -/
def claim11879_completedXiEvenJetThetaMomentRecurrence : Prop :=
  ∀ (h : ℕ → ℝ),
    completedXiEvenJet h →
      let t0 : ℝ := 2 - 4 * h 0
      thetaMomentSequence h t0 0 = t0 ∧
        (∀ j : ℕ,
          thetaMomentSequence h t0 (j + 1) =
            4 * (thetaMomentSequence h t0 j - h (j + 1))) ∧
          (∀ j : ℕ,
            checkerboardMoments h t0 j =
              (-1 : ℝ) ^ j * thetaMomentSequence h t0 j)

end

end MathlibPlus.Open.ResearchFormalization.O0182Claim11879
