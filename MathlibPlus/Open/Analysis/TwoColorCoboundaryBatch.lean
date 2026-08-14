import Mathlib

namespace MathlibPlus.Open.Analysis.TwoColorCoboundaryBatch

noncomputable section

open scoped BigOperators

/-- The two-colour kernel and its diagonal differential operator. -/
def k (t : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (5 * t / 2) * Real.exp (-Real.pi * Real.exp (2 * t))

def r (t : ℝ) : ℝ := Real.exp (2 * t)

def Lk (t : ℝ) : ℝ := -deriv (deriv k) t + (1 / 4) * k t

def F (t₁ t₂ : ℝ) : ℝ := k t₁ * k t₂

def beta (t₁ t₂ : ℝ) : ℝ :=
  2 * Real.pi * (r t₂ - r t₁) * F t₁ t₂

def diagonalDerivative (f : ℝ → ℝ → ℝ) (t₁ t₂ : ℝ) : ℝ :=
  deriv (fun x => f x t₂) t₁ + deriv (fun y => f t₁ y) t₂

def twoByTwoDet (a b c d : ℝ) : ℝ := a * d - b * c

def claim17871 : Prop :=
  ∀ t₁ t₂ : ℝ,
    twoByTwoDet (k t₁) (Lk t₁) (k t₂) (Lk t₂) =
      2 * Real.pi * diagonalDerivative
        (fun x y => (r y - r x) * F x y) t₁ t₂

def claim17872 : Prop :=
  ∀ t₁ t₂ : ℝ,
    twoByTwoDet (k t₁) (Lk t₁) (k t₂) (Lk t₂) = diagonalDerivative beta t₁ t₂ ∧
    beta t₂ t₁ = -beta t₁ t₂

def claim17873 : Prop :=
  (∀ t : ℝ, 0 < k t) ∧ StrictMono r ∧
    (∀ t₁ t₂ : ℝ, t₁ < t₂ → 0 < beta t₁ t₂) ∧
    (∀ t₁ t₂ : ℝ, beta t₂ t₁ = -beta t₁ t₂)

end
end MathlibPlus.Open.Analysis.TwoColorCoboundaryBatch
