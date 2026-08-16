import Mathlib
import Mathlib.Analysis.Distribution.Support

open scoped Distributions
open Set TopologicalSpace Distribution

namespace MathlibPlus.Open.AnalyticNumberTheory.CompactDistributionMoments

/-- Values of the `j`-th polynomial moment, represented by a compactly
supported smooth test function which agrees with the polynomial on an open
neighborhood of the actual distributional support. The final conjunct makes
the value independent of the chosen cutoff. -/
def compactDistributionMomentValues
    (T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ)) (j : ℕ) : Set ℂ :=
  {m | (∃ (U : Set ℝ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)),
      IsOpen U ∧ dsupport T ⊆ U ∧
        (∀ x : ℝ, x ∈ U → φ x = x ^ j) ∧
          T φ = m) ∧
    (∀ (U : Set ℝ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)),
      IsOpen U → dsupport T ⊆ U →
        (∀ x : ℝ, x ∈ U → φ x = x ^ j) → T φ = m)}

/-- Values of the exponential shift multiplier, using the real and imaginary
parts of the complex exponential as real test functions. The final conjunct
makes the value independent of the chosen cutoff. -/
def compactDistributionMultiplierValues
    (T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ)) (z : ℂ) : Set ℂ :=
  {m | (∃ (U : Set ℝ) (φre φim : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)),
      IsOpen U ∧ dsupport T ⊆ U ∧
        (∀ x : ℝ, x ∈ U →
          (φre x = (Complex.exp (-(x : ℂ) * z)).re ∧
            φim x = (Complex.exp (-(x : ℂ) * z)).im)) ∧
          T φre + Complex.I * T φim = m) ∧
    (∀ (U : Set ℝ) (φre φim : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)),
      IsOpen U → dsupport T ⊆ U →
        (∀ x : ℝ, x ∈ U →
          (φre x = (Complex.exp (-(x : ℂ) * z)).re ∧
            φim x = (Complex.exp (-(x : ℂ) * z)).im)) →
          T φre + Complex.I * T φim = m)}

/-- A nonzero value occurs among the canonical compact-support realizations
of the polynomial moment. -/
def hasNonzeroCompactDistributionMoment
    (T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ)) (j : ℕ) : Prop :=
  ∃ m : ℂ, m ∈ compactDistributionMomentValues T j ∧ m ≠ 0

/-- The entire multiplier is tied pointwise to the same distributional
pairing used for the moments. -/
def isEntireCompactDistributionMultiplier
    (T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ)) (M : ℂ → ℂ) : Prop :=
  Differentiable ℂ M ∧
    ∀ z : ℂ, M z ∈ compactDistributionMultiplierValues T z

/-- The derivatives at zero use the moments with the stated sign convention. -/
def compactDistributionMultiplierMomentIdentity
    (T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ)) (M : ℂ → ℂ) : Prop :=
  ∀ j : ℕ, ∃ m : ℂ,
    m ∈ compactDistributionMomentValues T j ∧
      iteratedDeriv j M 0 = (-1 : ℂ) ^ j * m

/-- Claim 15535: a nonzero compactly supported distribution has a least
index at which its polynomial moment is nonzero; the tied entire multiplier
has the corresponding derivatives at zero. -/
def claim15535 : Prop :=
  ∀ T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ),
    IsCompact (dsupport T) →
    T ≠ 0 →
    ∃ M : ℂ → ℂ,
      isEntireCompactDistributionMultiplier T M ∧
        compactDistributionMultiplierMomentIdentity T M ∧
        ∃ k : ℕ,
          hasNonzeroCompactDistributionMoment T k ∧
            ∀ j : ℕ, j < k →
              ∀ m : ℂ,
                m ∈ compactDistributionMomentValues T j → m = 0

end MathlibPlus.Open.AnalyticNumberTheory.CompactDistributionMoments
