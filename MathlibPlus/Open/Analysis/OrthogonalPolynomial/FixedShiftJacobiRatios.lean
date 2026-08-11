import Mathlib

/-!
# Fixed-shift Jacobi ratios and the Laurent right limit

Statement-fidelity formalization of admitted claim 479.  Because mathlib has no
principal real Lambert-W definition, `W₀` is characterized on the positive real axis
by positivity and `W₀(x) exp(W₀(x)) = x`.  The Laurent right limit is expanded
coefficientwise: after centering the zero-diagonal Jacobi matrix at row `n` and scaling
by `b n`, every fixed integer matrix entry tends to the corresponding entry of
`S + S⁻¹`.
-/

open Filter Topology

namespace MathlibPlus.Open.Analysis.OrthogonalPolynomial

/-- The asymptotic `bₙ ∼ π n / W₀(2n/e)` forces all fixed-shift ratios to tend to one
and gives the full-sequence Laurent right limit with symbol `w + w⁻¹`. -/
def fixedShiftJacobiRatiosAndLaurentLimit : Prop :=
  ∀ (W₀ : ℝ → ℝ) (b : ℕ → ℝ),
    (∀ x : ℝ, 0 < x → 0 < W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) →
    (∀ n : ℕ, 0 < n → 0 < b n) →
    Tendsto
      (fun n : ℕ =>
        b n /
          (Real.pi * (n : ℝ) /
            W₀ (2 * (n : ℝ) / Real.exp 1)))
      atTop (nhds 1) →
    (∀ k : ℤ,
      Tendsto
        (fun n : ℕ => b (Int.toNat ((n : ℤ) + k)) / b n)
        atTop (nhds 1)) ∧
    ∀ i j : ℤ,
      Tendsto
        (fun n : ℕ =>
          let row : ℤ := (n : ℤ) + i
          let col : ℤ := (n : ℤ) + j
          if 0 ≤ row ∧ 0 ≤ col ∧ (col = row + 1 ∨ row = col + 1) then
            b (Int.toNat (max row col)) / b n
          else 0)
        atTop
        (nhds (if j = i + 1 ∨ i = j + 1 then (1 : ℝ) else 0))

end MathlibPlus.Open.Analysis.OrthogonalPolynomial
