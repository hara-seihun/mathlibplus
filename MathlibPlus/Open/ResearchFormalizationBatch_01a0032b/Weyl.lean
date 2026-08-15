import Mathlib

open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section
open Classical
local instance weylPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section WeylSource

def superExponentialRealSource (Φ : ℝ → ℝ) : Prop :=
  Even Φ ∧ ∀ A : ℝ, 0 < A →
    Integrable (fun t => Real.exp (A * |t|) * |Φ t|) volume

def sourceTransform (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (Φ t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))

def sourceCorrelation (Φ : ℝ → ℝ) (y : ℝ) (sigma : ℂ) : ℂ :=
  ∫ d : ℝ, (Φ (y + d) : ℂ) * (Φ (y - d) : ℂ) *
    Complex.exp (Complex.I * sigma * (d : ℂ))

def sinOver (δ y : ℂ) : ℂ :=
  if δ = 0 then (y : ℂ) else Complex.sin (δ * y) / δ

def nonnegativeRealQuadraticForm (K : ℝ → ℝ → ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ ⊤ f → HasCompactSupport f →
    0 ≤ ∫ x : ℝ, ∫ y : ℝ, f x * K x y * f y

def coordinateWeylKernel (Φ : ℝ → ℝ) (ω a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ y : ℝ, (if |(a + b) / 2| ≤ y then
      y * Real.cosh (2 * ω * y) * Φ (y + (a - b) / 2) *
        Φ (y - (a - b) / 2) else 0)

def deBrangesKernelIntegral (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ) : ℂ :=
  (4 / Real.pi : ℂ) *
    ∫ y : ℝ in Set.Ici 0,
      sinOver (z - star w) (y : ℂ) *
        Complex.sinh (2 * (ω : ℂ) * (y : ℂ)) *
        sourceCorrelation Φ y (z + star w)

def weylCompressionIntegral (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ) : ℂ :=
  2 * ∫ y : ℝ in Set.Ici 0,
    (y : ℂ) * Complex.cosh (2 * (ω : ℂ) * (y : ℂ)) *
      sinOver (z - star w) (y : ℂ) * sourceCorrelation Φ y (z + star w)

def boundaryA (Φ : ℝ → ℝ) (ω p : ℝ) : ℂ :=
  sourceTransform Φ (p + (ω : ℂ) * Complex.I)

def boundaryDotA (Φ : ℝ → ℝ) (ω p : ℝ) : ℂ :=
  deriv (fun η : ℝ => sourceTransform Φ (p + (η : ℂ) * Complex.I)) ω

def boundaryAPrime (Φ : ℝ → ℝ) (ω p : ℝ) : ℂ :=
  deriv (fun q : ℝ => boundaryA Φ ω q) p

def boundaryDotAPrime (Φ : ℝ → ℝ) (ω p : ℝ) : ℂ :=
  deriv (fun q : ℝ => boundaryDotA Φ ω q) p

def complexMatrixPSD {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ c : Fin m → ℂ,
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, star (c i) * M i j * c j).re

def deBrangesFiniteGramPSD (Φ : ℝ → ℝ) (ω : ℝ) : Prop :=
  ∀ (m : ℕ) (z : Fin m → ℂ),
    (∀ j, 0 < (z j).im) →
      complexMatrixPSD (fun i j => deBrangesKernelIntegral Φ ω (z i) (z j))

/-- Claim 7576: the source correlation has both parity symmetries. -/
def sourceCorrelationParity : Prop :=
  ∀ (Φ : ℝ → ℝ), superExponentialRealSource Φ →
    ∀ (y : ℝ) (sigma : ℂ),
      sourceCorrelation Φ (-y) sigma = sourceCorrelation Φ y sigma ∧
      sourceCorrelation Φ y (-sigma) = sourceCorrelation Φ y sigma

/-- Claim 7582: the boundary diagonal limit with its exact negative sign. -/
def boundaryDiagonalLimitAndSign : Prop :=
  ∀ (Φ : ℝ → ℝ), superExponentialRealSource Φ →
    ∀ (ω : ℝ), 0 < ω → ∀ p : ℝ,
      weylCompressionIntegral Φ ω (p : ℂ) (p : ℂ) =
        (-1 / 4 : ℝ) *
          (boundaryDotAPrime Φ ω p * star (boundaryA Φ ω p)).im -
          (-1 / 4 : ℝ) *
          (boundaryDotA Φ ω p * star (boundaryAPrime Φ ω p)).im

/-- Claim 7584: positivity of every coordinate Weyl form transfers to de Branges Gram positivity. -/
def familyWeylPositivityTransfers : Prop :=
  ∀ (Φ : ℝ → ℝ) (ω : ℝ), superExponentialRealSource Φ → 0 < ω →
    (∀ η : ℝ, 0 < η → η < ω → nonnegativeRealQuadraticForm
      (coordinateWeylKernel Φ η)) →
    deBrangesFiniteGramPSD Φ ω

/-- Claim 7586: an upper-half-plane zero vetoes positivity throughout its height. -/
def genericOffAxisZeroCounterfeitVeto : Prop :=
  ∀ (Φ : ℝ → ℝ), superExponentialRealSource Φ →
    ∀ ζ : ℂ, 0 < ζ.im → sourceTransform Φ ζ = 0 →
      ¬ (∀ η : ℝ, 0 < η → η < ζ.im →
        nonnegativeRealQuadraticForm (coordinateWeylKernel Φ η))

def gaussianSource (α : ℝ) (t : ℝ) : ℝ := Real.exp (-α * t ^ 2)

def gaussianDeBrangesFormula (α ω : ℝ) (w z : ℂ) : ℂ :=
  let δ := z - star w
  let e := Complex.exp ((ω : ℂ) ^ 2 / (2 * α) -
    (z ^ 2 + (star w) ^ 2) / (4 * α))
  e * (1 / α) * sinOver δ ((ω : ℂ) / (2 * α))

def gaussianWeylFormula (α ω : ℝ) (w z : ℂ) : ℂ :=
  let δ := z - star w
  let e := Complex.exp ((ω : ℂ) ^ 2 / (2 * α) -
    (z ^ 2 + (star w) ^ 2) / (4 * α))
  (Real.pi / (8 * α ^ 2) : ℂ) * e *
    (Complex.cos ((ω : ℂ) * δ / (2 * α)) +
      2 * (ω : ℂ) * sinOver δ ((ω : ℂ) / (2 * α)))

/-- Claim 7590: the exact Gaussian de Branges and Weyl formulas. -/
def exactGaussianFixture : Prop :=
  ∀ (α ω : ℝ), 0 < α →
    ∀ (w z : ℂ),
      deBrangesKernelIntegral (gaussianSource α) ω w z =
        gaussianDeBrangesFormula α ω w z ∧
      weylCompressionIntegral (gaussianSource α) ω w z =
        gaussianWeylFormula α ω w z

end WeylSource

end

end MathlibPlus.Open.Batch_01a0032b
