import MathlibPlus.Open.ResearchFormalization.SourceFluxResistance

namespace MathlibPlus.Open.Research.FormalizationBatch.K0105Claim8602

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The Cholesky square-root relations used by the source and off-diagonal
conductance sequence. -/
def choleskyLiftRelations8602
    (alpha beta r s : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    alpha k = r k ^ 2 + s k ^ 2 ∧
      beta (k + 1) = r k * s (k + 1)

/-- The stagger and adjacent-variation terms in the interlaced square-root
lift. -/
def stagger8602 (r s : ℕ → ℝ) (k : ℕ) : ℝ :=
  s k ^ 2 - r (k - 1) ^ 2

def variationEnergy8602 (r s : ℕ → ℝ) (k : ℕ) : ℝ :=
  (s k - r (k - 1)) ^ 2 + (r k - s (k + 1)) ^ 2

/-- The weighted source formula and its bootstrap feedback term, with the
Jacobi, resistance, and Cholesky carriers kept explicit. -/
def feedbackIsTheEstimatedImbalance_claim8602 : Prop :=
  ∀ (n A B : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (alpha beta r s : ℕ → ℝ),
    1 ≤ A →
    A ≤ B →
    B ≤ n - 2 →
    positiveJacobi J alpha beta →
    choleskyLiftRelations8602 alpha beta r s →
    let Y : ℕ → ℝ := resistanceGaugeY J beta A
    let q : ℕ → ℝ :=
      fun k => leadingPrincipalDet J (k + 1) /
        leadingPrincipalDet J k
    let S : ℕ → ℝ := sourceCoordinate alpha beta
    let U : ℕ → ℝ := stagger8602 r s
    let E : ℕ → ℝ := variationEnergy8602 r s
    (∑ k ∈ Finset.Icc A B, S k * Y k) =
        (1 / 2 : ℝ) *
          (U A * Y A - U (B + 1) * Y B +
            ∑ k ∈ Finset.Icc (A + 1) B,
              U k * (Y k - Y (k - 1)) +
            ∑ k ∈ Finset.Icc A B, E k * Y k) ∧
      (∑ k ∈ Finset.Icc (A + 1) B,
        U k * (Y k - Y (k - 1))) =
        ∑ k ∈ Finset.Icc (A + 1) B,
          U k * Y (k - 1) *
            (q (k - 1) / beta k - 1)

end

end MathlibPlus.Open.Research.FormalizationBatch.K0105Claim8602
