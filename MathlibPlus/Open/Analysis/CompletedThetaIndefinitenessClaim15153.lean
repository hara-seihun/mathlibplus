import MathlibPlus.Open.Analysis.FiniteDivisibilityFirstLaguerre

open MeasureTheory
open scoped BigOperators ComplexOrder

namespace MathlibPlus.Open.Analysis.CompletedThetaIndefinitenessClaim15153

noncomputable section

/-- A constant linear feature of the positive completed-theta shell family. -/
noncomputable def shellFeature (w : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ, w n *
    (MathlibPlus.Open.Analysis.FiniteDivisibilityFirstLaguerre.shell (n + 1) u : ℂ)

/-- The unnormalised Fourier channel of a shell feature. -/
noncomputable def shellFeatureFourier (w : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp (-Complex.I * ((u * x : ℝ) : ℂ)) * shellFeature w u

/-- The literal Hermitian first-Laguerre contraction of two shell features. -/
noncomputable def shellFeatureFirstLaguerreEntry
    (w v : ℕ → ℂ) (x : ℝ) : ℂ :=
  (1 / 8 : ℂ) *
    (2 * starRingEnd ℂ (iteratedDeriv 1 (shellFeatureFourier w) x) *
        iteratedDeriv 1 (shellFeatureFourier v) x -
      starRingEnd ℂ (iteratedDeriv 2 (shellFeatureFourier w) x) *
        shellFeatureFourier v x -
      starRingEnd ℂ (shellFeatureFourier w x) *
        iteratedDeriv 2 (shellFeatureFourier v) x)

/-- The first-Laguerre matrix of a finite constant shell-feature family. -/
noncomputable def shellFeatureFirstLaguerreMatrix
    (features : Fin m → ℕ → ℂ) (x : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => shellFeatureFirstLaguerreEntry (features i) (features j) x

/-- Constant span containment of a cumulative divisibility channel by a
finite shell-feature family. -/
def shellFeatureSpanContains
    (features : Fin m → ℕ → ℂ) (q : ℕ) : Prop :=
  ∃ c : Fin m → ℂ, ∀ u : ℝ,
    (MathlibPlus.Open.Analysis.FiniteDivisibilityFirstLaguerre.cumulativeShell q u : ℂ) =
      ∑ i : Fin m, c i * shellFeature (features i) u

/-- Claim 15153.  Recovering two distinct positive cumulative divisibility
channels by constant shell features forces the literal central matrix to be
non-positive-semidefinite. -/
def recoveryOfTwoCumulativeChannelsForcesIndefinitenessClaim15153 : Prop :=
  ∀ (m : ℕ) (features : Fin m → ℕ → ℂ) (q r : ℕ),
    1 ≤ q →
    1 ≤ r →
    q ≠ r →
    shellFeatureSpanContains features q →
    shellFeatureSpanContains features r →
    ¬ (shellFeatureFirstLaguerreMatrix features 0).PosSemidef

end

end MathlibPlus.Open.Analysis.CompletedThetaIndefinitenessClaim15153
