import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Profiles

open MeasureTheory

noncomputable section

/-- The fixed Gaussian-Hermite profile appearing in the admitted source family. -/
def hProfile (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)

/-- The Gaussian profile appearing in the admitted source family. -/
def gProfile (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

/-- The bounded polynomial profile. -/
def boundedPolynomialWeight (m : ℕ) (lambda alpha beta x : ℝ) : ℝ :=
  (1 - x ^ 2 / lambda ^ 2) ^ m *
    (1 + (alpha * x ^ 2 + beta * x ^ 4) / lambda)

/-- The compactly supported source, with its balancing coefficient explicit. -/
def boundedPolynomialSource (m : ℕ) (lambda alpha beta d x : ℝ) : ℝ :=
  if |x| ≤ lambda then
    boundedPolynomialWeight m lambda alpha beta x * (hProfile x - d * gProfile x)
  else 0

/-- The weighted integral used to select the Gaussian coefficient. -/
def boundedPolynomialWeightedIntegral (m : ℕ) (lambda alpha beta : ℝ)
    (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, if |x| ≤ lambda then
    boundedPolynomialWeight m lambda alpha beta x * f x
  else 0

/-- The quotient selector when the weighted Gaussian denominator is nonzero. -/
def boundedPolynomialSelector (m : ℕ) (lambda alpha beta : ℝ) : ℝ :=
  boundedPolynomialWeightedIntegral m lambda alpha beta hProfile /
    boundedPolynomialWeightedIntegral m lambda alpha beta gProfile

/-- Gaussian coefficient re-selection and uniqueness for the compact source. -/
def gaussianCoefficientReselection : Prop :=
  ∀ (m : ℕ) (lambda alpha beta : ℝ), 1 ≤ m → 0 < lambda →
    let denominator :=
      boundedPolynomialWeightedIntegral m lambda alpha beta gProfile
    let numerator :=
      boundedPolynomialWeightedIntegral m lambda alpha beta hProfile
    denominator ≠ 0 →
      (∫ x : ℝ, boundedPolynomialSource m lambda alpha beta
          (numerator / denominator) x = 0) ∧
        ∀ d : ℝ,
          (∫ x : ℝ, boundedPolynomialSource m lambda alpha beta d x = 0) →
            d = numerator / denominator

/-- The L¹ distance of two real profiles. -/
def profileL1Distance (f g : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, ‖f x - g x‖

/-- Uniform O(lambda⁻¹) L¹ convergence on every compact transverse parameter set. -/
def boundedProfilesL1Convergence : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ S : Set (ℝ × ℝ), IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ p : ℝ × ℝ, p ∈ S →
            profileL1Distance
                (boundedPolynomialSource m lambda p.1 p.2
                  (boundedPolynomialSelector m lambda p.1 p.2))
                hProfile ≤ C / lambda

/-- The two exact Gaussian-Hermite center moments. -/
def exactGaussianHermiteCenterMoments : Prop :=
  (∫ x : ℝ, x ^ 2 * hProfile x = 3 / (2 * Real.pi ^ 2)) ∧
    (∫ x : ℝ, x ^ 4 * hProfile x = 15 / (2 * Real.pi ^ 3))

/-- The leading center functional, uniformly on compact transverse sets. -/
def leadingCenterFunctional : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ S : Set (ℝ × ℝ), IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ p : ℝ × ℝ, p ∈ S →
            |boundedPolynomialSource m lambda p.1 p.2
                (boundedPolynomialSelector m lambda p.1 p.2) 0 +
              (p.1 * (3 / (2 * Real.pi ^ 2)) +
                p.2 * (15 / (2 * Real.pi ^ 3))) / lambda| ≤ C / lambda ^ 2

/-- The center-orthogonal quartic profile. -/
def centerOrthogonalQuarticProfile (beta x : ℝ) : ℝ :=
  beta * (x ^ 4 - (5 / Real.pi) * x ^ 2)

/-- The exact second and fourth moments of the fixed profile. -/
def exactSecondAndFourthMoments : Prop :=
  (∫ x : ℝ, x ^ 2 * hProfile x = 3 / (2 * Real.pi ^ 2)) ∧
    (∫ x : ℝ, x ^ 4 * hProfile x = 15 / (2 * Real.pi ^ 3))

/-- The polynomial numerator used in the bounded-transverse expansion. -/
def quarticProfileNumerator (m : ℕ) (lambda beta : ℝ) : ℝ :=
  ∫ x : ℝ,
    (1 - x ^ 2 / lambda ^ 2) ^ m *
      (1 + centerOrthogonalQuarticProfile beta x / lambda) * hProfile x

/-- The corresponding Gaussian normalization denominator. -/
def quarticProfileDenominator (m : ℕ) (lambda beta : ℝ) : ℝ :=
  ∫ x : ℝ,
    (1 - x ^ 2 / lambda ^ 2) ^ m *
      (1 + centerOrthogonalQuarticProfile beta x / lambda) * gProfile x

/-- The coefficient obtained from the displayed numerator and denominator. -/
def quarticSelectedCoefficient (m : ℕ) (lambda beta : ℝ) : ℝ :=
  quarticProfileNumerator m lambda beta /
    quarticProfileDenominator m lambda beta

/-- The numerator expansion, uniformly over compact beta-sets. -/
def quarticNumeratorExpansion : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ S : Set ℝ, IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ beta : ℝ, beta ∈ S →
            |quarticProfileNumerator m lambda beta +
              (m : ℝ) * (3 / (2 * Real.pi ^ 2)) / lambda ^ 2| ≤ C / lambda ^ 3

/-- The denominator expansion, uniformly over compact beta-sets. -/
def quarticDenominatorExpansion : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ S : Set ℝ, IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ beta : ℝ, beta ∈ S →
            |quarticProfileDenominator m lambda beta - 1| ≤ C / lambda

/-- The selected coefficient expansion. -/
def selectedZeroIntegralCoefficientExpansion : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ S : Set ℝ, IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ beta : ℝ, beta ∈ S →
            |quarticSelectedCoefficient m lambda beta +
              (m : ℝ) * (3 / (2 * Real.pi ^ 2)) / lambda ^ 2| ≤ C / lambda ^ 3

/-- The exact quartic source used for its center value. -/
def quarticSource (m : ℕ) (lambda beta d x : ℝ) : ℝ :=
  if |x| ≤ lambda then
    (1 - x ^ 2 / lambda ^ 2) ^ m *
      (1 + centerOrthogonalQuarticProfile beta x / lambda) *
        (hProfile x - d * gProfile x)
  else 0

/-- The center-value expansion of the exact quartic source. -/
def quarticSourceCenterExpansion : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ S : Set ℝ, IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ beta : ℝ, beta ∈ S →
            |quarticSource m lambda beta
                (quarticSelectedCoefficient m lambda beta) 0 -
              (m : ℝ) * (3 / (2 * Real.pi ^ 2)) / lambda ^ 2| ≤ C / lambda ^ 3

/-- The exact endpoint coefficient from the quartic source. -/
def quarticEndpointCoefficient (m : ℕ) (lambda beta : ℝ) : ℝ :=
  -quarticSource m lambda beta (quarticSelectedCoefficient m lambda beta) 0 /
    (2 * Real.sqrt lambda)

/-- The nonzero Poisson-Dini endpoint scale, in an integer-power form of the
lambda asymptotic. -/
def quarticEndpointCoefficientExpansion : Prop :=
  ∀ (m : ℕ), 1 ≤ m → m ≠ 0 →
    ∀ S : Set ℝ, IsCompact S →
      ∃ C lambda₀ : ℝ, 0 ≤ C ∧ 0 < lambda₀ ∧
        ∀ lambda : ℝ, lambda₀ ≤ lambda →
          ∀ beta : ℝ, beta ∈ S →
            |quarticEndpointCoefficient m lambda beta +
              (3 * (m : ℝ)) /
                (4 * Real.pi ^ 2 * lambda ^ 2 * Real.sqrt lambda)| ≤
              C / (lambda ^ 3 * Real.sqrt lambda)

/-- The Euler operator D = x d/dx. -/
def eulerD (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x

/-- The shifted Euler operator -D(D+1). -/
def mathcalL (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -eulerD (fun y => eulerD f y + f y) x

/-- The shifted operator mathcal L - 1/4. -/
def mathcalZ (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => mathcalL f x - (1 / 4 : ℝ) * f x

end

end MathlibPlus.Open.ResearchFormalizationBatch.Profiles
