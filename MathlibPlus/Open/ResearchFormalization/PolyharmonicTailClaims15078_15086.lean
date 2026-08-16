import Mathlib
import MathlibPlus.Open.ResearchFormalization.FastOrderTailClaim15084

namespace MathlibPlus.Open.ResearchFormalization.PolyharmonicTailClaims15078_15086

open Filter MeasureTheory
open MathlibPlus.Open.ResearchFormalization.FastOrderTailClaim15084

noncomputable section

/-- The exponent in the first-saddle action, for the admissible orders `k ≥ 1`. -/
noncomputable def polyharmonicActionExponent (k : ℕ) : ℝ :=
  if 1 ≤ k then
    (2 * (k : ℝ)) / (2 * (k : ℝ) - 1)
  else 0

/-- The sharp first-saddle decay coefficient from the exact saddle action. -/
noncomputable def polyharmonicSharpAction (k : ℕ) : ℝ :=
  if 1 ≤ k then
    (2 * (k : ℝ) - 1) *
        Real.rpow (2 * (k : ℝ)) (-polyharmonicActionExponent k) *
      Real.sin (Real.pi / (4 * (k : ℝ) - 2))
  else 0

/-- A variable-rate lower envelope `T(L) ≥ exp (-(a(L)+o(1)) L)`. -/
def variableLowerExponentialEnvelope (T a : ℝ → ℝ) : Prop :=
  ∃ ε : ℝ → ℝ,
    Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ L : ℝ in atTop,
        T L ≥ Real.exp (-(a L + ε L) * L)

/-- The coefficient appearing in the finite positive-ratio tail estimate. -/
noncomputable def finiteRatioTailCoefficient
    (S : ℝ → ℝ) (k : ℝ → ℕ) (u η L : ℝ) : ℝ :=
  polyharmonicSharpAction (k L) *
      Real.rpow u (polyharmonicActionExponent (k L)) *
      Real.rpow (S L) (polyharmonicActionExponent (k L)) +
    η * u

/-- The finite-ratio bare-tail assertion with the schedule and kernel carrier fixed. -/
def finiteRatioBareTailClaim
    (S : ℝ → ℝ) (k : ℝ → ℕ) (u η q : ℝ) : Prop :=
  fastOrderSchedule S k →
    0 < u →
    0 ≤ η →
    0 < q →
    Tendsto (fun L : ℝ => (k L : ℝ) / S L) atTop (nhds q) →
    variableLowerExponentialEnvelope
      (polyharmonicAbsoluteTail S k u η)
      (finiteRatioTailCoefficient S k u η) ∧
    Tendsto (finiteRatioTailCoefficient S k u η)
      atTop (nhds (Real.pi * u / (4 * q) + η * u))

/-- Claim 15078: the sharp first-saddle constant has large-order limit `π/4`. -/
def largeOrderSharpConstant15078 : Prop :=
  Tendsto
    (fun k : ℕ => (k : ℝ) * polyharmonicSharpAction k)
    atTop (nhds (Real.pi / 4))

/-- Claim 15083: the finite positive `k_L/S_L` tail lower envelope. -/
def finitePositiveRatioTailLowerEnvelope15083 : Prop :=
  ∀ (S : ℝ → ℝ) (k : ℝ → ℕ) (u η q : ℝ),
    finiteRatioBareTailClaim S k u η q

/-- Absolute mass retained in a sublinear window, with an `e^{-o(L)}` lower bound. -/
def sublinearWindowAbsoluteMass
    (f : ℝ → ℝ → ℝ) (B : ℝ → ℝ) : Prop :=
  Tendsto (fun L : ℝ => B L / L) atTop (nhds 0) ∧
    (∀ᶠ L : ℝ in atTop, 0 ≤ B L) ∧
    ∃ ε : ℝ → ℝ,
      Tendsto ε atTop (nhds 0) ∧
        ∀ᶠ L : ℝ in atTop,
          (∫ s in Set.Icc (-B L) (B L), |f L s|) ≥
            Real.exp (-ε L * L)

/-- The positive weighted convolution majorant attached to the scheduled kernel. -/
noncomputable def scheduledPositiveConvolutionMajorant
    (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ)
    (u η L : ℝ) : ℝ :=
  ∫ t in Set.Ioi (u * L),
    Real.exp (-η * t) *
      (∫ s : ℝ,
        ‖MathlibPlus.Open.Research.O0263.polyharmonicKernel
          (scheduledPolyharmonicAlpha S k L) (k L) (t - s)‖ *
          |f L s|)

def qualifyingPositiveConvolutionCarrier
    (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ B : ℝ → ℝ, sublinearWindowAbsoluteMass f B

/-- A fixed nonzero `L¹` carrier, as named in the source special case. -/
def fixedNonzeroL1Carrier (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ 0 < ∫ s : ℝ, |f s|

/-- The finite-ratio majorant assertion used by Claim 15085. -/
def finiteRatioMajorantClaim
    (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ)
    (u η q : ℝ) : Prop :=
  fastOrderSchedule S k →
    0 < u →
    0 ≤ η →
    0 < q →
    qualifyingPositiveConvolutionCarrier f →
    Tendsto (fun L : ℝ => (k L : ℝ) / S L) atTop (nhds q) →
    variableLowerExponentialEnvelope
      (scheduledPositiveConvolutionMajorant S k f u η)
      (finiteRatioTailCoefficient S k u η) ∧
    Tendsto (finiteRatioTailCoefficient S k u η)
      atTop (nhds (Real.pi * u / (4 * q) + η * u))

/-- The infinite-ratio majorant assertion used by Claim 15085. -/
def infiniteRatioMajorantClaim
    (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ)
    (u η : ℝ) : Prop :=
  fastOrderSchedule S k →
    0 < u →
    0 ≤ η →
    qualifyingPositiveConvolutionCarrier f →
    Tendsto (fun L : ℝ => (k L : ℝ) / S L) atTop atTop →
    variableLowerExponentialEnvelope
      (scheduledPositiveConvolutionMajorant S k f u η)
      (fun _ : ℝ => η * u)

def fixedCarrierHasSublinearWindow : Prop :=
  ∀ f : ℝ → ℝ,
    fixedNonzeroL1Carrier f →
      ∃ B : ℝ → ℝ,
        sublinearWindowAbsoluteMass (fun _ : ℝ => f) B

/-- Claim 15085: positive convolution majorants inherit both bare-tail envelopes. -/
def positiveConvolutionMajorantsInheritTailEnvelope15085 : Prop :=
  (∀ (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ) (u η q : ℝ),
    finiteRatioMajorantClaim S k f u η q) ∧
  (∀ (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ) (u η : ℝ),
    infiniteRatioMajorantClaim S k f u η) ∧
  fixedCarrierHasSublinearWindow

/-- Big-Oh boundedness of the order-to-scale ratio. -/
def boundedOrderToScaleRatio
    (S : ℝ → ℝ) (k : ℝ → ℕ) : Prop :=
  ∃ C : ℝ,
    0 < C ∧
      ∀ᶠ L : ℝ in atTop,
        |(k L : ℝ) / S L| ≤ C

/-- Little-oh decay of a majorant relative to `exp (-A L)`. -/
def littleOExponential (M : ℝ → ℝ) (A : ℝ) : Prop :=
  Tendsto (fun L : ℝ => M L / Real.exp (-A * L)) atTop (nhds 0)

/-- A finite positive subsequential limit of `k_L/S_L`. -/
def finitePositiveRatioSubsequentialLimit
    (S : ℝ → ℝ) (k : ℝ → ℕ) (q : ℝ) : Prop :=
  0 < q ∧
    ∃ ℓ : ℕ → ℝ,
      Tendsto ℓ atTop atTop ∧
        Tendsto (fun n : ℕ => (k (ℓ n) : ℝ) / S (ℓ n))
          atTop (nhds q)

/-- Claim 15086: the absolute-error threshold forces bounded ratio and the stated
finite-limit inequality.  The majorant is the scheduled positive convolution,
not an unrelated function. -/
def necessaryBoundedRatioForAbsoluteError15086 : Prop :=
  ∀ (S : ℝ → ℝ) (k : ℝ → ℕ) (f : ℝ → ℝ → ℝ) (u η A : ℝ),
    fastOrderSchedule S k →
    0 < u →
    0 ≤ η →
    η * u < A →
    qualifyingPositiveConvolutionCarrier f →
    littleOExponential
      (scheduledPositiveConvolutionMajorant S k f u η) A →
    boundedOrderToScaleRatio S k ∧
      (∀ q : ℝ,
        finitePositiveRatioSubsequentialLimit S k q →
          q ≤ Real.pi * u / (4 * (A - η * u)))

end

end MathlibPlus.Open.ResearchFormalization.PolyharmonicTailClaims15078_15086
