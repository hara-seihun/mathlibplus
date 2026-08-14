import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.BatchO0296

noncomputable section
open Classical

def mobiusSpec (μ : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 0 < n →
    Finset.sum (Finset.Icc 1 n) (fun d => if d ∣ n then μ d else 0) = if n = 1 then 1 else 0

def commonDivisorIndicator {j : ℕ} (n : Fin j → ℕ) : ℤ :=
  if (∀ q : ℕ, (∀ i : Fin j, q ∣ n i) → q = 1) then 1 else 0

def diagonalTranslation {j : ℕ} (a : Fin j → ℝ)
    (f : (Fin j → ℝ) → ℝ) (x : Fin j → ℝ) : ℝ :=
  f (fun i => x i + a i)

def primeFace (p j : ℕ) (f : (Fin j → ℝ) → ℝ) (x : Fin j → ℝ) : ℝ :=
  f x - Real.rpow (p : ℝ) (-((j : ℝ) / 2)) *
    diagonalTranslation (fun _ : Fin j => Real.log p) f x

def claim15241 : Prop :=
  ∀ (j : ℕ), 0 < j →
    ∀ (n : Fin j → ℕ) (μ : ℕ → ℤ),
      (∀ i : Fin j, 0 < n i) →
      mobiusSpec μ →
      commonDivisorIndicator n =
        Finset.sum (Finset.Icc 1 (∏ i : Fin j, n i))
          (fun q => if (∀ i : Fin j, q ∣ n i) then μ q else 0) ∧
      (∀ (p : ℕ), Nat.Prime p →
        ∀ (f : (Fin j → ℝ) → ℝ) (x : Fin j → ℝ),
          primeFace p j f x =
            f x - Real.rpow (p : ℝ) (-((j : ℝ) / 2)) *
              f (fun i => x i + Real.log p))

end

end MathlibPlus.Open.Research.BatchO0296
