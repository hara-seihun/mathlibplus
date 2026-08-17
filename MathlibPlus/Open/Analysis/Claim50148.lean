import MathlibPlus.Open.Analysis.GammaReadout

namespace MathlibPlus.Open.Analysis

noncomputable section

open MeasureTheory

/-- The Laplace integral in Claim 50148, using the admitted order-one Borel
transform `gammaE`. -/
def gammaLaplaceIntegral50148 (m : ℕ) (z : ℂ) : ℂ :=
  ∫ v in Set.Ioi (0 : ℝ),
    (Real.exp (-v) : ℂ) * gammaE m (z * (v : ℂ))

/-- The pointwise integrand in the explicit Fubini majorant. -/
def gammaFubiniIntegrand50148 (z : ℂ) (v t : ℝ) : ℝ :=
  Real.exp (-v) *
    ‖Complex.exp (z * ((v * t : ℝ) : ℂ)) - 1‖

/-- Claim 50148: the half-plane Laplace identity, the compact-region Fubini
majorant, and integrability of every fixed logarithmic moment. -/
def claim50148 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    (∀ z : ℂ, z.re < 1 →
      gammaLaplaceIntegral50148 m z =
        (-Complex.log (1 - z)) ^ m) ∧
    (∀ (K : Set ℂ), IsCompact K →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
        K ⊆ {z : ℂ | z.re ≤ 1 - δ} →
          ∀ z : ℂ, z ∈ K →
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
              ∫ v in Set.Ioi (0 : ℝ),
                  gammaFubiniIntegrand50148 z v t ≤
                ‖z‖ * t / δ ^ 2) ∧
    (∀ p : ℕ,
      IntegrableOn (fun t : ℝ => |gammaL t| ^ p)
        (Set.Ioo (0 : ℝ) 1))

end

end MathlibPlus.Open.Analysis
