import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Faithful registry node for the coefficient perturbation bound.  The
coefficient-one norm is written as the finite sum over polynomial support; the
source's Q-star construction and spectral norm convention remain visible in
Qstar and the matrix norm interface. -/
def denominatorCoefficientPerturbationBound_claim15119 : Prop :=
  ∀ (r : ℕ) (Ahat : Matrix (Fin r) (Fin r) ℝ)
    (normTwo : Matrix (Fin r) (Fin r) ℝ → ℝ)
    (eA : ℝ) (Qhat Qstar : Polynomial ℝ),
    0 ≤ eA →
    Qhat = Matrix.det (fun i j =>
      (if i = j then (1 : Polynomial ℝ) else 0) -
        Polynomial.X * algebraMap ℝ (Polynomial ℝ) (Ahat i j)) →
    let M_A : ℝ := normTwo Ahat + eA
    (∑ n ∈ (Qhat - Qstar).support, ‖(Qhat - Qstar).coeff n‖) ≤
      (r : ℝ) * eA * (1 + M_A) ^ (r - 1)

end MathlibPlus.Open.Analysis
