import MathlibPlus.Open.ResearchFormalization.SourceFluxResistance

namespace MathlibPlus.Open.ResearchFormalization.K0105

noncomputable section

/-- Projective ratio of adjacent normalized continuants. -/
def projectiveRatioAdjacentNormalizedContinuants8585 : Prop :=
  ∀ (n a b : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (alpha beta : ℕ → ℝ),
    1 ≤ a →
    a ≤ b →
    b ≤ n - 2 →
    positiveJacobi J alpha beta →
    ∀ k : ℕ, a ≤ k → k ≤ b →
      let Y : ℕ → ℝ := resistanceGaugeY J beta a
      let q : ℕ → ℝ :=
        fun i => leadingPrincipalDet J (i + 1) / leadingPrincipalDet J i
      Y (k + 1) / Y k = q k / beta (k + 1)

end

end MathlibPlus.Open.ResearchFormalization.K0105
