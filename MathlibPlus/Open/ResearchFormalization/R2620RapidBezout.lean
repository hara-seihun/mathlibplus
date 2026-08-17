import MathlibPlus.Analysis.Claim42849

namespace MathlibPlus.Open.ResearchFormalization.R2620

/-- Claim 42852: exact Bézout extractors inherit every-degree rapid-decay
coefficient bound on the full real line. -/
def rapidDecayBezoutExtractors_claim42852 : Prop :=
  ∀ (A B H J : ℝ → ℂ) (C : ℕ → ℝ),
    (∀ t : ℝ, A t * H t + B t * J t = 1) →
    MathlibPlus.Analysis.Claim42849.jointlyRapidlyDecreasing H J C →
    ∀ (N : ℕ) (t : ℝ),
      (1 + |t|) ^ N ≤
        C N * max ‖A t‖ ‖B t‖

end MathlibPlus.Open.ResearchFormalization.R2620
