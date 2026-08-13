import MathlibPlus.Basic
import Mathlib.Probability.Distributions.Beta

namespace MathlibPlus.Analysis.Claim7259

/-- The absolute Jacobian of `(r,t) ↦ (rt,r(1-t))` is `r` for `r ≥ 0`. -/
theorem betaChangeOfVariablesJacobian_claim7259 (r t : ℝ) (hr : 0 ≤ r) :
    |Matrix.det (!![t, r; 1 - t, -r] : Matrix (Fin 2) (Fin 2) ℝ)| = r := by
  simp [Matrix.det_fin_two]
  rw [show -(t * r) - r * (1 - t) = -r by ring]
  rw [abs_neg, abs_of_nonneg hr]

/-- The Gamma/Beta factorization in the positive real-parameter region. -/
theorem gammaBetaFactorization_claim7259
    (w v : ℝ) (hw : 0 < w) (hv : 0 < v) :
    Real.Gamma (w + v) * ProbabilityTheory.beta (w + 1) v =
      Real.Gamma w * Real.Gamma v * w / (w + v) := by
  rw [ProbabilityTheory.beta]
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hwv : 0 < w + v := add_pos hw hv
  have hwv0 : w + v ≠ 0 := ne_of_gt hwv
  have hgwv : Real.Gamma (w + v) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hwv)
  have hgwv1 : Real.Gamma (w + v + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hwv zero_lt_one))
  rw [show w + 1 + v = (w + v) + 1 by ring,
    Real.Gamma_add_one (s := w + v) hwv0,
    Real.Gamma_add_one (s := w) hw0]
  field_simp

end MathlibPlus.Analysis.Claim7259
