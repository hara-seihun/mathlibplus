import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.CompletedZetaLoewner

/-- The exact finite scans of the total even completed-zeta Loewner matrix from
source record `C-0014`: every principal minor of orders two through seven on
the 25-rate pool is positive, and both displayed order-ten grids are positive
definite. -/
noncomputable def exhaustiveAdversarialFiniteScan : Prop :=
  let ξ : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) *
      Complex.Gamma (s / 2) * riemannZeta s
  let X : ℝ → ℝ := fun r => (ξ ((1 / 2 + r : ℝ) : ℂ)).re
  let L : ℝ → ℝ := fun r => deriv X r / X r
  let Q : {n : ℕ} → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun {_} rates i j =>
      if i = j then
        2 * (L (rates i) / rates i - deriv L (rates i))
      else
        4 * (rates j * L (rates i) - rates i * L (rates j)) /
          (rates j ^ 2 - rates i ^ 2)
  let pool : Fin 25 → ℝ :=
    ![500001 / 1000000, 50001 / 100000, 5001 / 10000, 501 / 1000,
      51 / 100, 13 / 25, 11 / 20, 29 / 50, 3 / 5, 2 / 3, 3 / 4,
      1, 5 / 4, 3 / 2, 2, 3, 5, 7, 10, 14, 20, 28, 40, 56, 80]
  let dyadic : Fin 10 → ℝ := fun j => 1 / 2 + 2 ^ (j : ℕ) / 10000
  let bridge : Fin 10 → ℝ :=
    ![5001 / 10000, 501 / 1000, 51 / 100, 11 / 20, 3 / 5,
      2 / 3, 3 / 4, 1, 5 / 4, 3 / 2]
  ((Finset.Icc 2 7).sum fun k => Nat.choose 25 k) = 726180 ∧
  (∀ (k : ℕ), 2 ≤ k → k ≤ 7 → ∀ select : Fin k → Fin 25,
    StrictMono select → 0 < Matrix.det (Q (fun i => pool (select i)))) ∧
  (∀ v : Fin 10 → ℝ, v ≠ 0 →
    0 < ∑ i, v i * ∑ j, Q dyadic i j * v j) ∧
  ∀ v : Fin 10 → ℝ, v ≠ 0 →
    0 < ∑ i, v i * ∑ j, Q bridge i j * v j

end MathlibPlus.Open.Analysis.CompletedZetaLoewner
