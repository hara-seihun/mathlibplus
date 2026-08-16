import Mathlib
import MathlibPlus.Analysis.ClaimDefinitions20260811
import MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386

open scoped BigOperators
open Filter MeasureTheory Set

namespace MathlibPlus.Open.Analysis.ResearchFormalizationPrimePowerCarrier01a00b9a

noncomputable section

abbrev PrimePowerIndex :=
  MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.PrimePowerIndex

abbrev PrimeIndex :=
  MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.PrimeIndex

abbrev PositiveIndex :=
  MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.PositiveIndex

noncomputable def primePowerA (pk : PrimePowerIndex) : ℝ :=
  MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.primeBernoulliA
    pk.1.1 pk.2.1

noncomputable def primePowerQ (pk : PrimePowerIndex) : ℝ :=
  MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.primeBernoulliQ
    pk.1.1 pk.2.1

noncomputable def primePowerProduct (z : ℂ) : ℂ :=
  ∏' pk : PrimePowerIndex,
    (1 - (primePowerQ pk : ℂ) * Complex.exp z)

noncomputable def primePowerProductReal (z : ℝ) : ℝ :=
  ∏' pk : PrimePowerIndex,
    (1 - primePowerQ pk * Real.exp z)

/-- The normal convergence condition for the exact prime-power product. -/
def primePowerNormalOn (K : Set ℂ) : Prop :=
  Summable (fun pk : PrimePowerIndex =>
    sSup ((fun z : ℂ =>
      ‖(primePowerQ pk : ℂ) * Complex.exp z‖) '' K))

/-- Claim 14253: the exact product has normal convergence, is entire, has the
specified prime-power zeros, and is positive on the negative real axis. -/
def claim14253 : Prop :=
  (∀ K : Set ℂ, IsCompact K → primePowerNormalOn K) ∧
  Differentiable ℂ primePowerProduct ∧
  (∀ pk : PrimePowerIndex,
    primePowerProduct (primePowerA pk : ℂ) = 0) ∧
  (∀ z : ℝ, z < 0 →
    (∀ pk : PrimePowerIndex,
      0 < 1 - primePowerQ pk * Real.exp z) ∧
    Summable (fun pk : PrimePowerIndex =>
      primePowerQ pk * Real.exp z) ∧
    primePowerProduct (z : ℂ) = (primePowerProductReal z : ℂ) ∧
    0 < primePowerProductReal z)

/-- The unordered elementary symmetric sums in the exact q-family. -/
noncomputable def primePowerElementary (m : ℕ) : ℝ :=
  ∑' S : {S : Finset PrimePowerIndex // S.card = m},
    Finset.prod S.1 (fun pk => primePowerQ pk)

/-- The convolution coefficients used by the negative-lattice pushforward. -/
noncomputable def primePowerD (m : ℕ) : ℝ :=
  Finset.sum (Finset.range (m + 1))
    (fun i => primePowerElementary i * primePowerElementary (m - i))

noncomputable def bernoulliSigmaSetValue (s : Set ℝ) : ℝ := by
  classical
  exact ∑' m : ℕ,
    if (m : ℝ) ∈ s then
      (-1 : ℝ) ^ m * primePowerElementary m
    else 0

/-- Exact atomic custody for the signed Bernoulli convolution. -/
def isBernoulliSigma (σ : SignedMeasure ℝ) : Prop :=
  σ ≠ 0 ∧
  IsFiniteMeasure σ.totalVariation ∧
  (∀ s : Set ℝ, MeasurableSet s →
    σ s = bernoulliSigmaSetValue s) ∧
  (∀ r : ℝ,
    Integrable (fun y : ℝ => Real.exp (r * y)) σ.totalVariation) ∧
  (∀ z : ℂ,
    Integrable (fun y : ℝ => Complex.exp (z * (y : ℂ))) σ.totalVariation)

/-- Claim 14254: the nonnegative elementary symmetric coefficients have the
exact plus-product moments, and their signed atomic measure has transform H. -/
def claim14254 : Prop :=
  (∀ m : ℕ, 0 ≤ primePowerElementary m) ∧
  (∀ r : ℝ,
    Summable (fun m : ℕ =>
      primePowerElementary m * Real.exp (r * (m : ℝ))) ∧
    HasProd
      (fun pk : PrimePowerIndex =>
        1 + primePowerQ pk * Real.exp r)
      (∏' (pk : PrimePowerIndex),
        (1 + primePowerQ pk * Real.exp r)) ∧
    (∑' (m : ℕ),
      (primePowerElementary m * Real.exp (r * (m : ℝ)))) =
      (∏' (pk : PrimePowerIndex),
        (1 + primePowerQ pk * Real.exp r))) ∧
  (∃ σ : SignedMeasure ℝ,
    isBernoulliSigma σ ∧
    (∀ z : ℂ,
      ∫ᵛ y : ℝ, Complex.exp (z * (y : ℂ)) ∂<•σ =
        primePowerProduct z))

noncomputable def negativeLatticeLocation (m : ℕ) : ℝ :=
  -(m : ℝ) / Real.log 2

noncomputable def negativeLatticeCoefficient (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) * primePowerD m * Real.exp (-(m : ℝ))

noncomputable def negativeLattice : Set ℝ :=
  Set.range negativeLatticeLocation

noncomputable def negativeLatticeSetValue (s : Set ℝ) : ℝ := by
  classical
  exact ∑' m : ℕ,
    if negativeLatticeLocation m ∈ s then
      negativeLatticeCoefficient m
    else 0

/-- Exact finite signed-measure and support conditions for the weighted
negative-lattice pushforward. -/
def isNegativeLatticeMeasure (μ : SignedMeasure ℝ) : Prop :=
  μ ≠ 0 ∧
  IsFiniteMeasure μ.totalVariation ∧
  (∀ s : Set ℝ, MeasurableSet s →
    μ s = negativeLatticeSetValue s) ∧
  μ (negativeLatticeᶜ) = 0 ∧
  (∀ x : ℝ, x ∈ negativeLattice → x ≤ 0) ∧
  ¬BddBelow negativeLattice

/-- Claim 14256: the exact weighted pushforward is a nonzero finite signed
measure on the unbounded negative lattice. -/
def claim14256 : Prop :=
  ∃ μ : SignedMeasure ℝ, isNegativeLatticeMeasure μ

noncomputable def muLaplaceTransform (μ : SignedMeasure ℝ) (t : ℝ) : ℝ :=
  ∫ᵛ y : ℝ, Real.exp (-t * y) ∂<•μ

noncomputable def completedKappa (t : ℝ) : ℝ :=
  MathlibPlus.Analysis.Claim15541.completedArchimedeanDensity t

noncomputable def highFrequencyDensity (μ : SignedMeasure ℝ) (t : ℝ) : ℝ :=
  completedKappa t * muLaplaceTransform μ t

noncomputable def highFrequencyAtom (μ : SignedMeasure ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) *
    muLaplaceTransform μ (Real.log (n : ℝ))

noncomputable def highFrequencyContinuousCarrier (μ : SignedMeasure ℝ) : Measure ℝ :=
  Measure.withDensity (volume.restrict (Ici (Real.log 2)))
    (fun t => ENNReal.ofReal (highFrequencyDensity μ t))

noncomputable def highFrequencyAtomicCarrier (μ : SignedMeasure ℝ) : Measure ℝ :=
  Measure.sum (fun n : {n : ℕ // 2 ≤ n} =>
    ENNReal.ofReal (highFrequencyAtom μ n.1) •
      Measure.dirac (Real.log (n.1 : ℝ)))

noncomputable def highFrequencyCarrier (μ : SignedMeasure ℝ) : Measure ℝ :=
  highFrequencyContinuousCarrier μ + highFrequencyAtomicCarrier μ

/-- Claim 14258: the exact completed high-frequency carrier has the stated
negative kappa, nonnegative continuous density, vanishing von Mangoldt atoms,
and nonzero locally finite Radon measure supported on the half-line. -/
def claim14258 : Prop :=
  ∃ μ : SignedMeasure ℝ,
    isNegativeLatticeMeasure μ ∧
    (∀ t : ℝ, Real.log 2 ≤ t → completedKappa t < 0) ∧
    (∀ t : ℝ, Real.log 2 ≤ t → 0 ≤ highFrequencyDensity μ t) ∧
    ContinuousOn (highFrequencyDensity μ) (Ici (Real.log 2)) ∧
    (∃ t : ℝ, Real.log 2 ≤ t ∧ highFrequencyDensity μ t ≠ 0) ∧
    (∀ n : ℕ, 2 ≤ n → highFrequencyAtom μ n = 0) ∧
    highFrequencyCarrier μ (Ici (Real.log 2))ᶜ = 0 ∧
    highFrequencyCarrier μ ≠ 0 ∧
    IsLocallyFiniteMeasure (highFrequencyCarrier μ) ∧
    IsFiniteMeasureOnCompacts (highFrequencyCarrier μ) ∧
    Measure.Regular (highFrequencyCarrier μ)

end
end MathlibPlus.Open.Analysis.ResearchFormalizationPrimePowerCarrier01a00b9a
