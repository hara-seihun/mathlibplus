import Mathlib

namespace MathlibPlus.Open.Analysis

private def finiteZeroDiagonalJacobiCoefficients8805
    (N : ℕ) (a : Fin (N + 1) → ℝ) : Prop :=
  a 0 = 0 ∧
    a (Fin.last N) = 0 ∧
      ∀ j : Fin (N + 1), 0 < j.val → j.val < N → 0 < a j

private def suffixFutureEdgeEnvelope8805
    (N : ℕ) (a A : Fin (N + 1) → ℝ) : Prop :=
  A (Fin.last N) = 0 ∧
    ∀ j : Fin N, 0 < j.val → j.val + 1 < N →
      (∀ ell : Fin N, j.val + 1 ≤ ell.val →
        a ell.castSucc ≤ A (Fin.succ j)) ∧
      (∃ ell : Fin N, j.val + 1 ≤ ell.val ∧
        A (Fin.succ j) = a ell.castSucc)

/-- The sharp variable action on the legal finite-Jacobi suffix domain. -/
def sharpVariableAction8805
    (N : ℕ) (a A : Fin (N + 1) → ℝ)
    (k r : ℕ) (lambda Isharp : ℝ) : Prop :=
  (hcoeff : finiteZeroDiagonalJacobiCoefficients8805 N a) →
    (henvelope : suffixFutureEdgeEnvelope8805 N a A) →
      (hkr : k < r) →
        (hr : r < N) →
          let k0 : Fin N := ⟨k, by omega⟩
          let k1 : Fin N := ⟨k + 1, by omega⟩
          let r0 : Fin N := ⟨r, by omega⟩
          lambda > 2 * A (Fin.succ k0) →
            Isharp =
              Finset.sum (Finset.Icc k1 r0) (fun j =>
                Real.log ((lambda + Real.sqrt (lambda ^ 2 - 4 * (A (Fin.succ j)) ^ 2)) /
                  (2 * a j.castSucc)))

end MathlibPlus.Open.Analysis
