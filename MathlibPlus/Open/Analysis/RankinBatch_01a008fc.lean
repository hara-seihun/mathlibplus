import Mathlib

namespace MathlibPlus.Open.Analysis.RankinBatch

noncomputable section

/-- The scalar-weight Fourier ray used by the admitted Rankin claims. -/
def fourierRay (k : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  y ^ (k / 2) * Real.exp (-2 * Real.pi * (n : ℝ) * y)

/-- The logarithmic derivative `L = y ∂_y`. -/
def logarithmicDerivative (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  y * deriv f y

/-- The second logarithmic jet `L²`. -/
def logarithmicDerivative₂ (f : ℝ → ℝ) : ℝ → ℝ :=
  logarithmicDerivative (fun z => logarithmicDerivative f z)

/-- The Fourier-ray coordinate `v = 4πny`. -/
def rayCoordinate (n : ℕ) (y : ℝ) : ℝ :=
  4 * Real.pi * (n : ℝ) * y

/-- The Mellin parameter `α = s + k - 1`. -/
def mellinAlpha (s : ℂ) (k : ℝ) : ℂ :=
  s + (k : ℂ) - 1

/-- The Rankin pairing with measure `y^(s-2) dy`. -/
def rankinPairing (s : ℂ) (f g : ℝ → ℝ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ),
    Complex.cpow (y : ℂ) (s - 2) * (f y : ℂ) * (g y : ℂ)

/-- The base Rankin moment on the Fourier ray. -/
def rankinI₀₀ (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ),
    Complex.cpow (y : ℂ) (s - 2) * (fourierRay k n y : ℂ) ^ 2

/-- The first Rankin jet moment. -/
def rankinI₁₀ (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  rankinPairing s
    (fun y => logarithmicDerivative (fourierRay k n) y)
    (fourierRay k n)

/-- The squared first-jet Rankin moment. -/
def rankinI₁₁ (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  rankinPairing s
    (fun y => logarithmicDerivative (fourierRay k n) y)
    (fun y => logarithmicDerivative (fourierRay k n) y)

/-- The second-jet Rankin moment. -/
def rankinI₂₀ (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  rankinPairing s
    (logarithmicDerivative₂ (fourierRay k n))
    (fourierRay k n)

/-- The moment of `v = 4πny` against the base Rankin density. -/
def rankinVMoment (s : ℂ) (k : ℝ) (n m : ℕ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ),
    ((rayCoordinate n y : ℂ) ^ m) *
      (Complex.cpow (y : ℂ) (s - 2) * (fourierRay k n y : ℂ) ^ 2)

/-- Claim 13432: the base moment is the stated Gamma law and all normalized
moments of `v` are the unit-rate Gamma moments of shape `α`. -/
def claim13432 : Prop :=
  ∀ (k : ℝ) (n : ℕ) (s : ℂ),
    0 < k → 1 ≤ n → 0 < (mellinAlpha s k).re →
      rankinI₀₀ s k n =
          Complex.Gamma (mellinAlpha s k) /
            Complex.cpow ((4 * Real.pi * (n : ℝ)) : ℂ) (mellinAlpha s k) ∧
      ∀ m : ℕ,
        rankinVMoment s k n m / rankinI₀₀ s k n =
          Complex.Gamma (mellinAlpha s k + (m : ℂ)) /
            Complex.Gamma (mellinAlpha s k)

/-- Claim 13433: the first two logarithmic jets on the Fourier ray. -/
def claim13433 : Prop :=
  ∀ (k : ℝ) (n : ℕ),
    0 < k → 1 ≤ n →
      ∀ y : ℝ, 0 < y →
        logarithmicDerivative (fourierRay k n) y /
            fourierRay k n y =
              (k - rayCoordinate n y) / 2 ∧
        logarithmicDerivative₂ (fourierRay k n) y /
            fourierRay k n y =
              ((rayCoordinate n y) ^ 2 - 2 * (k + 1) * rayCoordinate n y + k ^ 2) / 4

/-- Claim 13436: the weight-twelve specialization of the normalized moments. -/
def claim13436 : Prop :=
  ∀ (s : ℂ) (n : ℕ),
    1 ≤ n → 0 < (mellinAlpha s 12).re →
      rankinI₁₀ s 12 n / rankinI₀₀ s 12 n = (1 - s) / 2 ∧
      rankinI₁₁ s 12 n / rankinI₀₀ s 12 n = (s ^ 2 - s + 12) / 4 ∧
      rankinI₂₀ s 12 n / rankinI₀₀ s 12 n = (s - 5) * (s + 2) / 4

/-- Claim 13440: the difference of the first and second jet moments. -/
def claim13440 : Prop :=
  ∀ (k : ℝ) (n : ℕ) (s : ℂ),
    0 < k → 1 ≤ n → 0 < (mellinAlpha s k).re →
      (rankinI₁₁ s k n - rankinI₂₀ s k n) / rankinI₀₀ s k n =
        mellinAlpha s k / 2

end

end MathlibPlus.Open.Analysis.RankinBatch
