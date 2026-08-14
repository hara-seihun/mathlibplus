import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AdmittedBatch

/-- The complete homogeneous symmetric polynomial of degree `r` in `q` variables. -/
def completeHomogeneous (q r : ℕ) (xs : Fin q → ℝ) : ℝ :=
  ∑ e : Fin q → Fin (r + 1),
    if (∑ i : Fin q, (e i).val = r) then
      ∏ i : Fin q, (xs i) ^ (e i).val
    else 0

/-- The iterated forward difference with unit step. -/
def forwardDifference : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n + 1, f, x => forwardDifference n (fun y => f (y + 1) - f y) x

/-- The half-shifted type-B Stirling source matrix from Claim 57252. -/
def halfShiftedF (a : ℝ) (k n : ℕ) : ℝ :=
  if n < k then 0 else
    ((k + 1 : ℕ) : ℝ) *
      completeHomogeneous (k + 2) (n - k)
        (fun i : Fin (k + 2) => a + (i.val : ℝ))

/-- Claim 57252: the source-matrix formula and its finite-difference form agree. -/
def halfShiftedTypeBStirlingSourceMatrix : Prop :=
  ∀ (a : ℝ) (k n : ℕ),
    halfShiftedF a k n =
      forwardDifference (k + 1) (fun x : ℝ => x ^ (n + 1)) a /
        (Nat.factorial k : ℝ)

end MathlibPlus.Open.AdmittedBatch
