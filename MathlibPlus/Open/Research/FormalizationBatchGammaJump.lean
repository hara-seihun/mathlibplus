import MathlibPlus.Open.ResearchBatchMisc

namespace MathlibPlus.Open.Research.FormalizationBatchGammaJump

noncomputable section

open scoped BigOperators
open Filter
open Set
open Topology

open MathlibPlus.Open.ResearchBatchMisc

/-- The displayed positive density of the gamma jump form. -/
noncomputable def gammaJumpWeight (ell : ℝ) : ℝ :=
  Real.exp (-ell / 2) / (1 - Real.exp (-2 * ell))

/-- The localized gamma jump form from the admitted claim. -/
noncomputable def gammaJumpMetric (f : ℝ → ℝ) : ℝ :=
  ∫ ell in Set.Ioi (0 : ℝ), gammaJumpWeight ell * jumpEnergy (f := f) ell

/-- Claim 14930: strict positivity of the localized gamma-jump metric. -/
def claim_14930 : Prop :=
  ∀ (R : ℝ), 0 < R →
    (∃ δ : ℝ, 0 < δ ∧
      ∀ (g : ℝ → ℝ), HasCompactSupport g →
        Function.support g ⊆ Set.Icc (-R) R →
        δ * realL2Squared (f := g) ≤ gammaJumpMetric g) ∧
    ∀ (f : ℝ → ℝ), HasCompactSupport f →
      Function.support f ⊆ Set.Icc (-R) R →
      (∀ ell : ℝ, 2 * R < ell →
        Disjoint (Function.support (fun x => f (x + ell)))
          (Function.support f) ∧
          jumpEnergy (f := f) ell = 2 * realL2Squared (f := f)) ∧
      (0 < realL2Squared (f := f) → 0 < gammaJumpMetric f)

/-- The common-cutoff coefficient `a_n = Λ(n) / √n`. -/
noncomputable def primeJumpCoefficient (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)

/-- The prime contribution at the same finite cutoff as the jump sum. -/
noncomputable def primeCorrelationCutoff (X : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 X,
    -2 * primeJumpCoefficient n *
      autocorrelation (f := f) (Real.log (n : ℝ))

/-- The uncompensated prime jump sum at a finite cutoff. -/
noncomputable def primeJumpCutoff (X : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 X,
    primeJumpCoefficient n *
      jumpEnergy (f := f) (Real.log (n : ℝ))

/-- The scalar counterterm at a common prime cutoff. -/
noncomputable def primeCounterterm (X : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 2 X, primeJumpCoefficient n

/-- The cutoff-dependent killing scalar forced by exact compensation. -/
noncomputable def cutoffKillingScalar (X : ℕ) : ℝ :=
  -primeCounterterm X

/-- The compensated prime jump sum at a common cutoff. -/
noncomputable def compensatedPrimeSum (X : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 X,
    primeJumpCoefficient n *
      (jumpEnergy (f := f) (Real.log (n : ℝ)) -
        2 * realL2Squared (f := f))

/-- Claim 14931: prime powers are compensated jumps at a common cutoff. -/
def claim_14931 : Prop :=
  ∀ (f : ℝ → ℝ), HasCompactSupport f →
    (∀ (n : ℕ), 2 ≤ n →
      -2 * primeJumpCoefficient n *
          autocorrelation (f := f) (Real.log (n : ℝ)) =
        primeJumpCoefficient n *
            jumpEnergy (f := f) (Real.log (n : ℝ)) -
          2 * primeJumpCoefficient n * realL2Squared (f := f)) ∧
    (∀ (X : ℕ),
      compensatedPrimeSum X f =
        primeJumpCutoff X f + cutoffKillingScalar X *
          realL2Squared (f := f))

/-- Translate a real test function to the right by `ell`. -/
def translateRight (ell : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (x - ell)

/-- The two equal translated copies used for the negative compensated atom. -/
def equalSeparatedPair (ell : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  f + translateRight ell f

/-- The same pair with one copy's sign reversed. -/
def oppositeSeparatedPair (ell : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  f - translateRight ell f

/-- Claim 14936: every compensated jump atom is indefinite. -/
def claim_14936 : Prop :=
  (∀ (f : ℝ → ℝ), HasCompactSupport f →
    ∀ ell : ℝ,
      jumpEnergy (f := f) ell - 2 * realL2Squared (f := f) =
        -2 * autocorrelation (f := f) ell) ∧
  ∀ ell : ℝ, 0 < ell →
    ∃ (a : ℝ) (bump : ℝ → ℝ),
      0 < a ∧ a < ell ∧
      HasCompactSupport bump ∧
      Function.support bump ⊆ Set.Icc 0 a ∧
      0 < realL2Squared (f := bump) ∧
      HasCompactSupport (equalSeparatedPair ell bump) ∧
      HasCompactSupport (oppositeSeparatedPair ell bump) ∧
      jumpEnergy (f := equalSeparatedPair ell bump) ell -
          2 * realL2Squared (f := equalSeparatedPair ell bump) < 0 ∧
      0 < jumpEnergy (f := oppositeSeparatedPair ell bump) ell -
          2 * realL2Squared (f := oppositeSeparatedPair ell bump)

/-- Claim 14937: no cutoff-independent killing repair exists. -/
def claim_14937 : Prop :=
  (∀ (f : ℝ → ℝ) (X : ℕ), HasCompactSupport f →
    primeJumpCutoff X f + cutoffKillingScalar X *
        realL2Squared (f := f) =
      primeCorrelationCutoff X f) ∧
  Tendsto cutoffKillingScalar atTop atBot ∧
  Tendsto
    (fun X : ℕ => cutoffKillingScalar X / (-4 * Real.sqrt (X : ℝ)))
    atTop (𝓝 1) ∧
  ¬ ∃ κ : ℝ,
    ∀ (f : ℝ → ℝ), HasCompactSupport f →
      ∃ q : ℝ,
        Tendsto
          (fun X : ℕ => primeJumpCutoff X f +
            κ * realL2Squared (f := f))
          atTop (𝓝 q) ∧
        Tendsto (fun X : ℕ => primeCorrelationCutoff X f)
          atTop (𝓝 q)

end

end MathlibPlus.Open.Research.FormalizationBatchGammaJump
