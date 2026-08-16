import MathlibPlus.Open.Research.FormalizationBatch.O0191Fiber
import MathlibPlus.Open.Research.FormalizationBatch.O0191Parity

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch.O0191LocalChannel

noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch.O0191Parity
open MathlibPlus.Open.Research.FormalizationBatchGammaJump
open MathlibPlus.Open.ResearchBatchMisc

abbrev LocalH_R (R : ℝ) : Type :=
  MathlibPlus.Open.Research.FormalizationBatch.O0191Parity.H_R R

/-- The localized finite-cutoff jump form, with the prime sum ending at `X`. -/
noncomputable def primeCutoffLForm (R : ℝ) (X : ℕ)
    (f g : LocalH_R R) : ℝ :=
  (∫ ell : ℝ in Ioi (0 : ℝ),
      gammaJumpWeight ell * jumpBilinear R ell f g) +
    ∑ n ∈ Finset.Icc 2 X,
      primeJumpCoefficient n *
        jumpBilinear R (Real.log (n : ℝ)) f g

/-- The common-cutoff scalar in the negative channel.  The fixed completed
constant is retained in addition to the variable prime mass. -/
noncomputable def primeCutoffKappa (X : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 2 X, primeJumpCoefficient n +
    Real.log Real.pi - (Complex.digamma (1 / 4 : ℂ)).re

/-- The positive channel energy of the finite colligation. -/
noncomputable def positiveChannelEnergy (R : ℝ) (X : ℕ) (f : LocalH_R R) : ℝ :=
  primeCutoffLForm R X f f + pCoordinate R f ^ 2

/-- The negative channel map, including the fixed scalar and the polar
coordinate.  Its target is recorded as the pair of the Hilbert component and
its scalar polar component. -/
noncomputable def negativeChannel (R : ℝ) (X : ℕ) (f : LocalH_R R) :
    LocalH_R R × ℝ :=
  (Real.sqrt (primeCutoffKappa X) • f, mCoordinate R f)

/-- The Hilbert direct-sum square of a pair.  This is the squared norm of the
negative colligation `D_X f` in its two orthogonal channel components. -/
def channelSquareNorm {R : ℝ} (u : LocalH_R R × ℝ) : ℝ :=
  ‖u.1‖ ^ 2 + u.2 ^ 2

noncomputable def negativeChannelNormSq
    (R : ℝ) (X : ℕ) (f : LocalH_R R) : ℝ :=
  primeCutoffKappa X * ‖f‖ ^ 2 + mCoordinate R f ^ 2

/-- The increment of the positive channel at one prime-power atom. -/
noncomputable def positivePrimeIncrement
    (R : ℝ) (n : ℕ) (f : LocalH_R R) : ℝ :=
  primeJumpCoefficient n *
    jumpBilinear R (Real.log (n : ℝ)) f f

/-- The increment of the negative channel at the same atom. -/
noncomputable def negativePrimeIncrement
    (R : ℝ) (n : ℕ) (f : LocalH_R R) : ℝ :=
  2 * primeJumpCoefficient n * cutoffInner f f

/-- The zero-extended representative used when the stabilized difference is
written as the finite prime correlation form. -/
def localizedRepresentative (R : ℝ) (f : LocalH_R R) : ℝ → ℝ :=
  Set.indicator (Ioo (-R) R) (f : ℝ → ℝ)

/-- Claim 14947: the two channels of the exact local colligation acquire the
same divergent prime mass, and all shifts beyond the support diameter are
neutral in their difference. -/
def claim_14947 : Prop :=
  ∀ (R : ℝ), 0 < R →
    ∀ f : LocalH_R R,
      MathlibPlus.Open.Research.FormalizationBatch.O0191Fiber.compactlySupported
        R f → f ≠ 0 →
        ∃ d : ℝ,
          MathlibPlus.Open.Research.FormalizationBatch.O0191Fiber.supportDiameterBound
              R f d ∧
            Tendsto
              (fun X : ℕ => positiveChannelEnergy R X f)
              atTop atTop ∧
            Tendsto
              (fun X : ℕ => negativeChannelNormSq R X f)
              atTop atTop ∧
            (∀ X : ℕ, Real.exp d < (X : ℝ) →
              positiveChannelEnergy R X f - negativeChannelNormSq R X f =
                primeCorrelationCutoff X (localizedRepresentative R f)) ∧
            (∀ X Y : ℕ,
              Real.exp d < (X : ℝ) → X ≤ Y →
                positiveChannelEnergy R X f - negativeChannelNormSq R X f =
                  positiveChannelEnergy R Y f - negativeChannelNormSq R Y f) ∧
            (∀ n : ℕ, Real.exp d < (n : ℝ) →
              positivePrimeIncrement R n f = negativePrimeIncrement R n f ∧
                autocorrelation (f := localizedRepresentative R f)
                    (Real.log (n : ℝ)) = 0)

end

end MathlibPlus.Open.Research.FormalizationBatch.O0191LocalChannel
