import Mathlib
import MathlibPlus.Open.ResearchFormalization.FastOrderTailClaim15084

namespace MathlibPlus.Open.ResearchFormalization.PositiveHeightDiniThresholdClaim15087

open Filter MeasureTheory
open scoped Topology

noncomputable section

open MathlibPlus.Open.Research.O0263
open MathlibPlus.Open.ResearchFormalization.FastOrderTailClaim15084

/-- The absolute positive convolution majorant of the scheduled kernel. -/
noncomputable def positiveConvolutionMajorant
    (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ)
    (u η L : ℝ) : ℝ :=
  ∫ t in Set.Ioi (u * L),
    Real.exp (-η * t) *
      (∫ s : ℝ,
        ‖polyharmonicKernel (scheduledPolyharmonicAlpha S k L) (k L) (t - s)‖ *
          |f L s|)

/-- An input profile retains subexponential absolute mass in a sublinear window. -/
def retainsSubexponentialWindowMass (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ B : ℝ → ℝ,
    Tendsto (fun L : ℝ => B L / L) atTop (𝓝 0) ∧
      (∀ᶠ L : ℝ in atTop, 0 ≤ B L) ∧
      ∃ ε : ℝ → ℝ,
        Tendsto ε atTop (𝓝 0) ∧
          ∀ᶠ L : ℝ in atTop,
            ∫ s in Set.Icc (-B L) (B L), |f L s| ≥
              Real.exp (-ε L * L)

/-- The little-oh condition for a positive majorant at exponential rate `A`. -/
def exponentiallyNegligible (M : ℝ → ℝ) (A : ℝ) : Prop :=
  Tendsto (fun L : ℝ => M L / Real.exp (-A * L)) atTop (𝓝 0)

/-- A majorant is either the bare absolute tail or an absolute convolution
majorant whose input retains the source's subexponential window mass. -/
def qualifyingPositiveMajorant
    (S : ℝ → ℝ) (k : ℝ → ℕ) (M : ℝ → ℝ) (u η : ℝ) : Prop :=
  M = polyharmonicAbsoluteTail S k u η ∨
    ∃ f : ℝ → ℝ → ℝ,
      retainsSubexponentialWindowMass f ∧
        M = fun L : ℝ => positiveConvolutionMajorant S k f u η L

/-- A finite positive subsequential limit of the growing-order ratio `k_L/S_L`. -/
def finitePositiveRatioSubsequence
    (S : ℝ → ℝ) (k : ℝ → ℕ) (q : ℝ) : Prop :=
  0 < q ∧
    ∃ ℓ : ℕ → ℝ,
      Tendsto ℓ atTop atTop ∧
        Tendsto
          (fun n : ℕ => (k (ℓ n) : ℝ) / S (ℓ n))
          atTop (𝓝 q)

/-- Claim 15087: after substituting `A = 5/2-y` and `η = y` in the
necessary threshold for an absolute majorant, the two specified tails impose
the stated bounds on every finite positive subsequential ratio. -/
def positiveHeightDiniThresholdsClaim15087 : Prop :=
  ∀ (S : ℝ → ℝ) (k : ℝ → ℕ) (y q : ℝ)
    (MHalf MOne : ℝ → ℝ),
    fastOrderSchedule S k →
      0 < y →
        finitePositiveRatioSubsequence S k q →
          ((0 < (5 / 2 : ℝ) - 3 * y / 2) →
              (qualifyingPositiveMajorant S k MHalf ((1 / 2 : ℝ)) y →
                (exponentiallyNegligible MHalf ((5 / 2 : ℝ) - y) →
                  q ≤ Real.pi /
                    (8 * ((5 / 2 : ℝ) - 3 * y / 2))))) ∧
            ((0 < (5 / 2 : ℝ) - 2 * y) →
              (qualifyingPositiveMajorant S k MOne (1 : ℝ) y →
                (exponentiallyNegligible MOne ((5 / 2 : ℝ) - y) →
                  q ≤ Real.pi /
                    (4 * ((5 / 2 : ℝ) - 2 * y)))))

end

end MathlibPlus.Open.ResearchFormalization.PositiveHeightDiniThresholdClaim15087
