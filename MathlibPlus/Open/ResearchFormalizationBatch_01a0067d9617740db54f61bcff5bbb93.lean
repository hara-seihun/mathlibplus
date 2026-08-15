import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a0067d9617740db54f61bcff5bbb93

def higherOrderCompactKernelSetup
    (L : ℝ) (r : ℕ) (K : ℝ → ℝ)
    (B : (ℝ → ℝ) → ℝ → ℝ)
    (U : ℕ → ℝ → ℝ)
    (T : ℂ → ℂ)
    (F : ℂ → ℂ) : Prop :=
  B = (fun (f : ℝ → ℝ) (x : ℝ) =>
    -deriv (deriv f) x + (1 / 4 : ℝ) * f x) ∧
  U = (fun j => B^[j] K) ∧
  T = (fun z => z ^ 2 + (1 / 4 : ℂ)) ∧
  F = (fun z =>
    ∫ t in (0 : ℝ)..L,
      (K t : ℂ) * Complex.cos
        (z * ((t : ℂ) - ((L / 2 : ℝ) : ℂ)))) ∧
  ∀ q : ℕ, 0 ≤ q ∧ q ≤ 2 * r - 1 →
    (deriv^[q] K) L = 0

def endpointDefectCoordinates
    (A : ℝ) (K : ℝ → ℝ)
    (B : (ℝ → ℝ) → ℝ → ℝ)
    (U : ℕ → ℝ → ℝ)
    (α β : ℕ → ℝ) : Prop :=
  A ≠ 0 ∧
  B = (fun (f : ℝ → ℝ) (x : ℝ) =>
    -deriv (deriv f) x + (1 / 4 : ℝ) * f x) ∧
  U = (fun j => B^[j] K) ∧
  (∀ j : ℕ,
    α j = U j 0 - A * (if j = 0 then 1 else 0)) ∧
  (∀ j : ℕ,
    β j = deriv (U j) 0 - (A / 2) * (if j = 0 then 1 else 0))

def diniCellGeometry
    (L : ℝ) (Y : ℝ) (n r : ℕ) (K : ℝ → ℝ)
    (B : (ℝ → ℝ) → ℝ → ℝ)
    (U : ℕ → ℝ → ℝ)
    (x X C S d q Q Z ρ : ℝ) : Prop :=
  0 < Y ∧
  Y < 1 / 2 ∧
  0 < n ∧
  B = (fun (f : ℝ → ℝ) (t : ℝ) =>
    -deriv (deriv f) t + (1 / 4 : ℝ) * f t) ∧
  U = (fun j => B^[j] K) ∧
  x = (2 * (n : ℝ) - 1) * Real.pi / L ∧
  X = (2 * (n : ℝ) + 1) * Real.pi / L ∧
  C = Real.cosh (L * Y / 2) ∧
  S = Real.sinh (L * Y / 2) ∧
  d = min (x - S / 2) (x * S - C / 2) ∧
  q = x ^ 2 - Y ^ 2 + 1 / 4 ∧
  Q = X ^ 2 + Y ^ 2 + 1 / 4 ∧
  Z = Real.sqrt (X ^ 2 + Y ^ 2) ∧
  ρ = ∫ t in (0 : ℝ)..L, |U r t|

def explicitPerCellRoucheCriterion
    (L : ℝ) (r : ℕ) (K : ℝ → ℝ) (A Y : ℝ) (n : ℕ)
    (B : (ℝ → ℝ) → ℝ → ℝ)
    (U : ℕ → ℝ → ℝ)
    (T : ℂ → ℂ)
    (F : ℂ → ℂ)
    (α β : ℕ → ℝ)
    (x X C S d q Q Z ρ : ℝ) : Prop :=
  B = (fun (f : ℝ → ℝ) (t : ℝ) =>
    -deriv (deriv f) t + (1 / 4 : ℝ) * f t) ∧
  U = (fun j => B^[j] K) ∧
  T = (fun z => z ^ 2 + (1 / 4 : ℂ)) ∧
  F = (fun z =>
    ∫ t in (0 : ℝ)..L,
      (K t : ℂ) * Complex.cos
        (z * ((t : ℂ) - ((L / 2 : ℝ) : ℂ)))) ∧
  (∀ k : ℕ, 0 ≤ k ∧ k ≤ 2 * r - 1 →
    (deriv^[k] K) L = 0) ∧
  A ≠ 0 ∧
  (∀ j : ℕ,
    α j = U j 0 - A * (if j = 0 then 1 else 0)) ∧
  (∀ j : ℕ,
    β j = deriv (U j) 0 - (A / 2) * (if j = 0 then 1 else 0)) ∧
  0 < Y ∧
  Y < 1 / 2 ∧
  0 < n ∧
  x = (2 * (n : ℝ) - 1) * Real.pi / L ∧
  X = (2 * (n : ℝ) + 1) * Real.pi / L ∧
  C = Real.cosh (L * Y / 2) ∧
  S = Real.sinh (L * Y / 2) ∧
  d = min (x - S / 2) (x * S - C / 2) ∧
  q = x ^ 2 - Y ^ 2 + 1 / 4 ∧
  Q = X ^ 2 + Y ^ 2 + 1 / 4 ∧
  Z = Real.sqrt (X ^ 2 + Y ^ 2) ∧
  ρ = ∫ t in (0 : ℝ)..L, |U r t| ∧
  ((d > 0 ∧ q > 0 ∧
      |A| * q ^ (r - 1) * d >
        C * (ρ +
          ∑ j ∈ Finset.range r,
            Q ^ (r - 1 - j) * (Z * |α j| + |β j|))) →
    ∃ z : ℂ,
      (x ≤ z.re ∧ z.re ≤ X ∧ |z.im| ≤ Y) ∧
      F z = 0 ∧
      (∀ w : ℂ,
        (x ≤ w.re ∧ w.re ≤ X ∧ |w.im| ≤ Y) →
          F w = 0 → w = z) ∧
      (∃ m : ℕ,
        m = 1 ∧
        (∀ k : ℕ, k < m → (deriv^[k] F) z = 0) ∧
        (deriv^[m] F) z ≠ 0) ∧
      z.im = 0 ∧
      deriv F z ≠ 0)

end MathlibPlus.Open.ResearchFormalizationBatch_01a0067d9617740db54f61bcff5bbb93
