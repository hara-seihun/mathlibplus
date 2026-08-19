import Mathlib

noncomputable section

namespace MathlibPlus.Open.Algebra.Claim11839

private noncomputable def witnessPolynomial11839 : Polynomial ℤ :=
  (1 + Polynomial.X) ^ 10 *
    (1 + 13 * Polynomial.X) *
    (1 + 14 * Polynomial.X) ^ 2

private def ordinaryCoefficient11839 (k : ℕ) : ℤ :=
  witnessPolynomial11839.coeff k

private def factorialCoefficient11839 (k : ℕ) : ℤ :=
  (Nat.factorial k : ℤ) * ordinaryCoefficient11839 k

def exactCoefficientPrefix_claim11839 : Prop :=
  (fun k : Fin 9 => ordinaryCoefficient11839 k.1) =
      ![1, 51, 1015, 10113, 55810, 190722, 433902, 684930, 764661] ∧
    (fun k : Fin 9 => factorialCoefficient11839 k.1) =
      ![1, 51, 2030, 60678, 1339440, 22886640, 312409440,
        3452047200, 30831131520]

end MathlibPlus.Open.Algebra.Claim11839

end
