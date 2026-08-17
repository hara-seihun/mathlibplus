import MathlibPlus.Open.ResearchFormalization.CompletedThetaMonic11882

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.CompletedThetaBulk11881

noncomputable section

open MathlibPlus.Open.ResearchFormalization.CompletedTheta11882

/-- The completed-theta checkerboard bulk entry with the signed moments and all
boundary-shifted Bezout terms retained. -/
def claim11881 : Prop :=
  ∀ h : ℕ → ℝ, completedXiEvenJet h →
    let t0 : ℝ := 2 - 4 * h 0
    let c : ℕ → ℝ := checkerboardMoments h t0
    ∀ (N : ℕ) (i j : Fin N),
      checkerboardBulk h t0 N i j =
        (-1 : ℝ) ^ (i.1 + j.1) *
          (((((i.1 + j.1 + 1 : ℕ) : ℝ) / 2) *
              (c (i.1 + j.1) + (1 / 4 : ℝ) * c (i.1 + j.1 + 1)) +
            (1 / 16 : ℝ) * completedThetaBezoutEntry c (i.1 : ℤ) (j.1 : ℤ) +
            (1 / 4 : ℝ) *
              completedThetaBezoutEntry c ((i.1 : ℤ) - 1) (j.1 : ℤ) +
            (1 / 4 : ℝ) *
              completedThetaBezoutEntry c (i.1 : ℤ) ((j.1 : ℤ) - 1) +
            completedThetaBezoutEntry c
              ((i.1 : ℤ) - 1) ((j.1 : ℤ) - 1)))

end

end MathlibPlus.Open.ResearchFormalization.CompletedThetaBulk11881
