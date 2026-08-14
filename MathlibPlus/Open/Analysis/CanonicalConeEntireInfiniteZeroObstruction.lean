import Mathlib

open Complex

namespace MathlibPlus.Open.Analysis

/--
There are explicit real and complex functions with the stated positivity,
continuation, symmetry, and upper-half-plane zero properties.
-/
def canonicalConeEntireInfiniteZeroObstruction : Prop :=
  ∃ (P : ℝ → ℝ) (H : ℕ → ℝ → ℝ) (F : ℂ → ℂ) (z : ℕ → ℂ),
    P = (fun x : ℝ => Real.exp (2 * Real.pi * x) + Real.exp (-2 * Real.pi * x) + 2) ∧
    H = (fun _ : ℕ => fun q : ℝ => q) ∧
    F = (fun w : ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * w) +
        Complex.exp (-2 * (Real.pi : ℂ) * w) + 2) ∧
    z = (fun n : ℕ => ((n : ℂ) + (1 / 2 : ℂ)) * Complex.I) ∧
    P 0 ≠ 0 ∧
    (∀ N : ℕ, ∀ y : ℝ, 0 < H N (P (-y) / P 0)) ∧
    Differentiable ℂ F ∧
    (∀ x : ℝ, F (x : ℂ) = (P x : ℂ)) ∧
    (∀ w : ℂ, F (-w) = F w) ∧
    (∀ w : ℂ, F (starRingEnd ℂ w) = starRingEnd ℂ (F w)) ∧
    Function.Injective z ∧
    (∀ n : ℕ, F (z n) = 0) ∧
    (∀ n : ℕ, 0 < (z n).im)

end MathlibPlus.Open.Analysis
