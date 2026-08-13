import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim6218

/-- The finite-support multiplicity sequence corresponding to `(t_j)_{j≥0}`. -/
def admissible (ell N : ℕ) (t : ℕ →₀ ℕ) : Prop :=
  t.sum (fun _ k => k) = ell ∧
    (∑ j ∈ t.support, j * t j) = N

/-- The polynomial product attached to a finitely supported multiplicity sequence. -/
noncomputable def factorProduct (t : ℕ →₀ ℕ) : MvPolynomial (Fin 2) ℚ :=
  ∏ j ∈ t.support,
    (1 + MvPolynomial.X (0 : Fin 2) *
      (MvPolynomial.X (1 : Fin 2)) ^ j) ^ (t j)

/-- The rational polynomial span in claim 6218. -/
noncomputable def monomialSpan (ell N : ℕ) :
    Submodule ℚ (MvPolynomial (Fin 2) ℚ) :=
  Submodule.span ℚ
    {p : MvPolynomial (Fin 2) ℚ |
      ∃ t : ℕ →₀ ℕ, admissible ell N t ∧ p = factorProduct t}

/-- `D(ell,N)`, the dimension of the span in claim 6218. -/
noncomputable def D (ell N : ℕ) : ℕ := Module.finrank ℚ (monomialSpan ell N)

end MathlibPlus.Algebra.Claim6218
