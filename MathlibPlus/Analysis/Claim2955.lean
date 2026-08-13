import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim2955

open Polynomial

noncomputable section

/-- The polynomial sequence obtained from the first-shell differentiation
recurrence, with the analytic prefactor stripped away. -/
def Q : ℕ → Polynomial ℚ
  | 0 => C 2 * X - C 3
  | n + 1 =>
      (C (5 / 2 : ℚ) - C 2 * X) * Q n +
        C 2 * X * derivative (Q n)

/-- The generalized-Bell polynomial sequence used in the exact first-shell
identification. -/
def H : ℕ → Polynomial ℚ
  | 0 => X - C (3 / 2 : ℚ)
  | n + 1 =>
      (X - C (5 / 4 : ℚ)) * H n -
        X * derivative (H n)

/-- Exact generalized-Bell identification for the polynomial recurrence in
claim 2955: `Q n = 2^(n+1) (-1)^n H n`.  The source's separate analytic
identification of `Q` with derivatives of `phi₁` is retained as an alignment
boundary rather than silently assumed here. -/
theorem Q_eq_scale_H_claim2955 (n : ℕ) :
    Q n = ((2 : ℚ) ^ (n + 1) * (-1 : ℚ) ^ n) • H n := by
  have recurrence (c : ℚ) (p : Polynomial ℚ) :
      (C (5 / 2 : ℚ) - C 2 * X) * (c • p) +
          C 2 * X * derivative (c • p) =
        (-2 * c) • ((X - C (5 / 4 : ℚ)) * p -
          X * derivative p) := by
    have h52 : C (5 / 2 : ℚ) = (2 : ℚ) • C (5 / 4 : ℚ) := by
      rw [Polynomial.smul_eq_C_mul]
      rw [← Polynomial.C_mul]
      congr 1
      norm_num
    have h2X : C (2 : ℚ) * X = (2 : ℚ) • X := by
      rw [Polynomial.smul_eq_C_mul]
    rw [Polynomial.derivative_smul]
    rw [mul_smul_comm, mul_smul_comm]
    simp only [smul_sub]
    rw [h52, h2X]
    rw [← smul_sub]
    rw [smul_mul_assoc]
    rw [smul_smul]
    rw [smul_mul_assoc]
    rw [smul_smul]
    rw [show (-2 * c : ℚ) = c * (-2) by ring]
    rw [← smul_smul c (-2)]
    rw [← smul_smul c (-2)]
    simp only [Polynomial.smul_eq_C_mul]
    rw [Polynomial.C_mul]
    rw [Polynomial.C_neg]
    ring
  induction n with
  | zero =>
      rw [Q, H, Polynomial.smul_eq_C_mul]
      have hbase : C (3 : ℚ) = C 2 * C (3 / 2 : ℚ) := by
        rw [← Polynomial.C_mul]
        congr 1
        norm_num
      rw [hbase]
      ring
  | succ n ih =>
      rw [Q, ih]
      rw [show H (n + 1) =
        (X - C (5 / 4 : ℚ)) * H n -
          X * derivative (H n) by rfl]
      have hc :
          (2 : ℚ) ^ (n + 2) * (-1 : ℚ) ^ (n + 1) =
            -2 * ((2 : ℚ) ^ (n + 1) * (-1 : ℚ) ^ n) := by
        rw [pow_succ, pow_succ]
        ring
      rw [hc]
      exact recurrence _ _

end
end MathlibPlus.Analysis.Claim2955
