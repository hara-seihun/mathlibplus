import MathlibPlus.Open.ResearchFormalization.C0089

namespace MathlibPlus.Open.ResearchFormalization.C0089Claim1345

open MathlibPlus.Open.ResearchFormalization.C0089

noncomputable section

/-- The exact suffix maximum value used for the exceptional cell. -/
noncomputable def alpha (N : ℕ) : ℝ :=
  sSup (B '' Set.Ici (N : ℝ))

/-- Claim 1345: the coefficient-`1.15` suffix maximum is attained at the
specified prime, with the exact prime count, strict start separation, and the
strict comparison against every other prime before the inherited C-0081
handoff. -/
def exceptionalCoefficient115Optimizer_claim1345 : Prop :=
  let N : ℕ := 38284442297
  let pStar : ℕ := 38284442321
  let inheritedTailHandoff : ℕ := 42575222481
  Nat.Prime pStar ∧
    primeCounting (pStar : ℝ) = 1641621296 ∧
    (N : ℝ) ≤ (pStar : ℝ) ∧
    (∀ x : ℝ, (N : ℝ) ≤ x → B x ≤ B (pStar : ℝ)) ∧
    alpha N = B (pStar : ℝ) ∧
    B (pStar : ℝ) - B (N : ℝ) >
      (5228375 : ℝ) / (10 : ℝ) ^ 15 ∧
    (∀ p : ℕ, Nat.Prime p → N < p → p < inheritedTailHandoff →
      p ≠ pStar → B (p : ℝ) < B (pStar : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.C0089Claim1345
