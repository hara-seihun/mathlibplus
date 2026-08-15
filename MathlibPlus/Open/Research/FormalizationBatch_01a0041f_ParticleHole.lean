import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

def nodePolynomial (n : ℕ) (x : Fin n → ℝ) (X : ℝ) : ℝ :=
  ∏ i : Fin n, (X - x i)

def dualHoleWeight (n : ℕ) (x w : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 / (w i * (deriv (nodePolynomial n x) (x i)) ^ 2)

def particleVandermonde (n : ℕ) (x : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  Finset.prod S (fun i =>
    Finset.prod (S.filter (fun j => i < j)) (fun j => x j - x i))

def particlePartition (n k : ℕ) (x u : Fin n → ℝ) : ℝ :=
  Finset.sum (Finset.univ.powerset.filter (fun S => S.card = k)) (fun S =>
    particleVandermonde n x S ^ 2 * Finset.prod S (fun i => u i))

def gaussianMoment (n : ℕ) (x w : Fin n → ℝ) (a : ℕ) : ℝ :=
  ∑ i : Fin n, w i * (x i) ^ a

def gaussianHankel (n k : ℕ) (x w : Fin n → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => gaussianMoment n x w (i.1 + j.1)

def shiftedGaussianHankel (n k : ℕ) (x w : Fin n → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => gaussianMoment n x w (i.1 + j.1 + 1)

def gaussianDelta (n k : ℕ) (x w : Fin n → ℝ) : ℝ :=
  Matrix.det (gaussianHankel n k x w)

def shiftedGaussianDelta (n k : ℕ) (x w : Fin n → ℝ) : ℝ :=
  Matrix.det (shiftedGaussianHankel n k x w)

def dualHoleWeightsOverNodes (n : ℕ) (x w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => dualHoleWeight n x w i / x i

/-- Particle-hole complement identities for the ordinary and shifted rules. -/
def claim_8571 : Prop :=
  ∀ n : ℕ, ∀ (x w : Fin n → ℝ),
    (∀ i j, i ≠ j → x i ≠ x j) →
    (∀ i, 0 < w i) →
    (∀ i, x i ≠ 0) →
    ∀ m : ℕ, m ≤ n →
      gaussianDelta n (n - m) x w =
          gaussianDelta n n x w *
            particlePartition n m x (dualHoleWeight n x w) ∧
      shiftedGaussianDelta n (n - m) x w =
          shiftedGaussianDelta n n x w *
            particlePartition n m x (dualHoleWeightsOverNodes n x w)

end
end MathlibPlus.Open.Research
