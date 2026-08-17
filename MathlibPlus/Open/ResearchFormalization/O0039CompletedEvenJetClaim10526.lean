import MathlibPlus.Open.ResearchFormalizationBatch_GammaBezout

namespace MathlibPlus.Open.ResearchFormalization.O0039CompletedEvenJetClaim10526

open MathlibPlus.Open.ResearchFormalizationBatch_GammaBezout
open scoped BigOperators

noncomputable section

/--
Claim 10526: the completed even-jet cell is positive, has the exact
factorially normalized shifted-Gamma moments, and the displayed positive
column scaling preserves strict total positivity on that carrier.
-/
def claim10526_completedEvenJetCellRealization : Prop :=
  ∀ α : ℝ, 0 < α →
    (∀ (p : ℕ) (v : ℝ), 0 < v →
      0 < completedCell α p v) ∧
    (∀ (p q : ℕ),
      completedJetMomentFromCell α p q = completedJetMoment α p q) ∧
    strictCompletedJetTotalPositivity α ∧
    (∀ (r : ℕ) (p q : Fin r → ℕ),
      StrictMono p → StrictMono q →
        0 < Matrix.det (fun i j : Fin r =>
          risingFactorial α (p i + q j)) →
        0 < Matrix.det (fun i j : Fin r =>
          completedJetMoment α (p i) (q j)))

end

end MathlibPlus.Open.ResearchFormalization.O0039CompletedEvenJetClaim10526
