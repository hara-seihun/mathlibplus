import Mathlib

namespace MathlibPlus.Open.Research.K0160

noncomputable section
open Classical
open scoped BigOperators

 def primeSequence (p : ℕ → ℕ) : Prop :=
  p 0 = 2 ∧ (∀ k, Nat.Prime (p k) ∧ p k < p (k + 1)) ∧
    (∀ q, Nat.Prime q → ∃ k, p k = q)

def primorial (p : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (k + 1), p j

def theta (p : ℕ → ℕ) (k : ℕ) : ℝ :=
  Real.log (primorial p k : ℝ)

def nicolasRatio (p : ℕ → ℕ) (k : ℕ) : ℝ :=
  (primorial p k : ℝ) /
    (Nat.totient (primorial p k) : ℝ) /
    Real.log (Real.log (primorial p k : ℝ))

def primeEulerProduct (p : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∏ q ∈ (Finset.Icc 2 (p k)).filter Nat.Prime, (1 - (q : ℝ)⁻¹)⁻¹

def claim9195 (p : ℕ → ℕ) (k : ℕ) : Prop :=
  primeSequence p ∧
    nicolasRatio p k = primeEulerProduct p k / Real.log (theta p k) ∧
    nicolasRatio p k =
      (∏ j ∈ Finset.range (k + 1),
        (1 - (p j : ℝ)⁻¹)⁻¹) / Real.log (theta p k)

def claim9197 (p : ℕ → ℕ) (k : ℕ)
    (q L y Δ : ℝ) : Prop :=
  primeSequence p ∧ q = p (k + 1) ∧ L = Real.log q ∧ y = theta p k ∧
    Δ = -Real.log (1 - 1 / q) -
      Real.log (Real.log (y + L) / Real.log y) ∧
    Δ = Real.log (nicolasRatio p (k + 1)) - Real.log (nicolasRatio p k)

end

end MathlibPlus.Open.Research.K0160

namespace MathlibPlus.Open.Research.K0161

noncomputable section

 def quartetPoint (δ γ : ℝ) : ℂ :=
  (1 / 2 + δ : ℝ) + (γ : ℂ) * Complex.I

def claim9214 (δ γ y a b : ℝ) : Prop :=
  δ > 0 →
    let ρ : ℂ := quartetPoint δ γ
    let c : ℂ := 1 / (ρ * (1 - ρ))
    let Q : ℝ :=
      4 * (a * Real.cosh (δ * y) * Real.cos (γ * y) -
        b * Real.sinh (δ * y) * Real.sin (γ * y))
    c = (a : ℂ) + (b : ℂ) * Complex.I ∧
      Q = 2 * Real.exp (δ * y) *
          (c * Complex.exp (Complex.I * (γ * y))).re +
        2 * Real.exp (-δ * y) *
          (c * Complex.exp (Complex.I * (-(γ * y)))).re

end

end MathlibPlus.Open.Research.K0161

namespace MathlibPlus.Open.Research.K0162

noncomputable section
open Classical

 def divisibilityMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if (i.val + 1) ∣ (j.val + 1) then 1 else 0

def mobiusMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j =>
    if (i.val + 1) ∣ (j.val + 1) then
      ((ArithmeticFunction.moebius ((j.val + 1) / (i.val + 1)) : ℤ) : ℚ)
    else 0

def claim9224 (n : ℕ) : Prop :=
  (divisibilityMatrix n)⁻¹ = mobiusMatrix n

end

end MathlibPlus.Open.Research.K0162
