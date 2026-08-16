import Mathlib

open scoped BigOperators
open MeasureTheory
open Set

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.TransformDeflation

/-- The even completed-theta kernel occurring in the admitted transform formula. -/
def completedThetaKernel (u : ℝ) : ℝ :=
  ∑' n : ℕ, if 0 < n then
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
    else 0

/-- The Green-kernel one-zero deflation from the admitted statement. -/
def deflatedThetaKernel (γ u : ℝ) : ℝ :=
  γ * ∫ v in Set.Ioi u, completedThetaKernel v * Real.sin (γ * (v - u))

/-- The completed transform represented by the theta kernel. -/
def completedThetaTransform (z : ℂ) : ℂ :=
  2 * ∫ u in Set.Ioi (0 : ℝ),
    (completedThetaKernel u : ℂ) * Complex.cosh ((u : ℂ) * Complex.sqrt z)

/-- The transform represented by the one-zero-deflated kernel. -/
def deflatedThetaTransform (γ : ℝ) (z : ℂ) : ℂ :=
  2 * ∫ u in Set.Ioi (0 : ℝ),
    (deflatedThetaKernel γ u : ℂ) * Complex.cosh ((u : ℂ) * Complex.sqrt z)

/-- Iterated ordinary derivatives, with the derivative operator made explicit. -/
def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  ((fun g : ℝ → ℝ => deriv g)^[n]) f

/-- Coefficients with the structural zero convention for negative indices. -/
def deflatedIndexCoeff (γ : ℝ) (m : ℤ) : ℂ :=
  if 0 ≤ m then
    (2 : ℂ) / (Nat.factorial (2 * m.toNat) : ℂ) *
      ∫ u in Set.Ioi (0 : ℝ),
        (deflatedThetaKernel γ u : ℂ) * (u : ℂ) ^ (2 * m.toNat)
  else 0

/-- The ordered positive chamber in the exact Andreief integral. -/
def orderedPositiveChamber (r : ℕ) : Set (Fin r → ℝ) :=
  {u | (∀ i, 0 < u i) ∧ ∀ i j, i < j → u i < u j}

/-- The Wronskian determinant in the deflated ordered-chamber formula. -/
def deflatedChamberDet (γ : ℝ) (r : ℕ) (u : Fin r → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    iterDeriv (2 * i.1) (deflatedThetaKernel γ) (u j))

/-- The moment product in the deflated ordered-chamber formula. -/
def deflatedMomentProduct (r k : ℕ) (u : Fin r → ℝ) : ℝ :=
  ∏ ℓ : Fin r, u ℓ ^ (2 * k)

/-- The ordered Vandermonde product in the deflated ordered-chamber formula. -/
def orderedVandermonde (r : ℕ) (u : Fin r → ℝ) : ℝ :=
  ∏ p : Fin r, ∏ q : Fin r,
    if p < q then u q ^ 2 - u p ^ 2 else 1

/-- The denominator product in the deflated Andreief formula. -/
def evenFactorialProduct (r k : ℕ) : ℝ :=
  ∏ j : Fin r, (Nat.factorial (2 * (k + j.1)) : ℝ)

/-- The exact ordered-chamber integral after replacing Φ by Φγ. -/
def deflatedChamberIntegral (γ : ℝ) (r k : ℕ) : ℝ :=
  ∫ u in orderedPositiveChamber r,
    deflatedChamberDet γ r u * deflatedMomentProduct r k u *
      orderedVandermonde r u

/-- The rectangular Toeplitz minor formed from the deflated coefficients. -/
def deflatedMinor (γ : ℝ) (r k : ℕ) : ℂ :=
  Matrix.det (fun i j : Fin r =>
    deflatedIndexCoeff γ (Int.ofNat (k + j.1) - Int.ofNat i.1))

/-- Exact transform factorization, coefficient shift, and ordered-chamber formula
for every positive one-zero deflation.  This is an open statement: no proof is
claimed here. -/
def exactTransformFactorizationAfterOneZeroDeflation : Prop :=
  ∀ γ : ℝ, 0 < γ →
    completedThetaTransform (-((γ : ℂ) ^ 2)) = 0 →
    (∀ z : ℂ,
      completedThetaTransform z =
        (1 + z / (γ : ℂ) ^ 2) * deflatedThetaTransform γ z) ∧
    (∀ z : ℂ, 1 + z / (γ : ℂ) ^ 2 ≠ 0 →
      deflatedThetaTransform γ z =
        completedThetaTransform z / (1 + z / (γ : ℂ) ^ 2)) ∧
    (∀ m : ℤ, m < 0 → deflatedIndexCoeff γ m = 0) ∧
    (∀ N i : ℕ,
      deflatedIndexCoeff γ (Int.ofNat N - Int.ofNat i) =
        (2 : ℂ) / (Nat.factorial (2 * N) : ℂ) *
          ∫ u in Set.Ioi (0 : ℝ),
            (iterDeriv (2 * i) (deflatedThetaKernel γ) u : ℂ) *
              (u : ℂ) ^ (2 * N)) ∧
    (∀ r k : ℕ,
      deflatedMinor γ r k =
        ((2 : ℂ) ^ r / (evenFactorialProduct r k : ℂ)) *
          (deflatedChamberIntegral γ r k : ℂ))


