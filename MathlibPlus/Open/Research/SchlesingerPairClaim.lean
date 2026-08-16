import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

def explicitTauVisibleDiagonalPair_claim11475 : Prop :=
  let A_p : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![1, 0], ![0, -1]]
  let A_q : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![2, 0], ![0, -2]]
  let tauFactor : ℝ → ℝ → ℝ := fun x y => (x - y) ^ 4
  let pairLogTerm : ℝ → ℝ → ℝ := fun x y =>
    4 * Real.log |x - y|
  let mixedHessian : ℝ → ℝ → ℝ := fun x y =>
    deriv (fun x' => deriv (fun y' => pairLogTerm x' y') y) x
  (A_p * A_q = A_q * A_p) ∧
    Matrix.trace (A_p * A_q) = 4 ∧
    (∀ a_p a_q : ℝ, a_p ≠ a_q →
      tauFactor a_p a_q = (a_p - a_q) ^ 4 ∧
      Real.exp (pairLogTerm a_p a_q) = tauFactor a_p a_q ∧
      mixedHessian a_p a_q = 4 / (a_p - a_q) ^ 2 ∧
      mixedHessian a_p a_q ≠ 0)

end MathlibPlus.Open.Research.FormalizationBatch
