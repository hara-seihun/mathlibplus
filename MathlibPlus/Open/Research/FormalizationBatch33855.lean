import Mathlib

namespace MathlibPlus.Open

/--
The bounded-variable polynomial setup from admitted claim 33855.  The outer
polynomial variable is `z`; its coefficients are multivariate polynomials in
exactly the variables indexed by `Fin c`.  The parameter `q` is independent
of `c`, so the residual degree is not bounded by the context weight.
-/
def boundedVariablePolynomialSetup
    (c q : ℕ)
    (C H : Polynomial (MvPolynomial (Fin c) ℤ)) : Prop :=
  C.Monic ∧
    C.natDegree = c ∧
    H.natDegree = q ∧
    ∃ (cCoeff : Fin (c + 1) → MvPolynomial (Fin c) ℤ)
      (hCoeff : Fin (q + 1) → MvPolynomial (Fin c) ℤ),
      C = ∑ i : Fin (c + 1),
        Polynomial.X ^ (i : ℕ) * Polynomial.C (cCoeff i) ∧
      cCoeff ⟨c, Nat.lt_succ_self c⟩ = 1 ∧
      H = ∑ a : Fin (q + 1),
        Polynomial.X ^ (a : ℕ) * Polynomial.C (hCoeff a)

end MathlibPlus.Open
