import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

abbrev booleanCubeFunction (n : ℕ) := (Fin n → Bool) → Bool

def affineBarycenter
    (n : ℕ) (μ : booleanCubeFunction n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ h, μ h * boolSign (h x)

def affineCoordinateMass (n : ℕ) (t : Fin n → ℝ) : ℝ :=
  ∑ i, |t i|

def affineCoordinateEnergy (n : ℕ) (t : Fin n → ℝ) : ℝ :=
  ∑ i, (t i) ^ 2

def affineBarycenterCoefficientConstraints
    (n : ℕ) (μ : booleanCubeFunction n → ℝ)
    (c : ℝ) (t : Fin n → ℝ) : Prop :=
  (∀ h, 0 ≤ μ h) ∧
  (∑ h, μ h = 1) ∧
  (∀ x,
    affineBarycenter n μ x = c + ∑ i, t i * boolSign (x i)) →
  (affineCoordinateMass n t ≤ 1 - |c| ∧ 1 - |c| ≤ 1)

end MathlibPlus.Open.ResearchFormalization
