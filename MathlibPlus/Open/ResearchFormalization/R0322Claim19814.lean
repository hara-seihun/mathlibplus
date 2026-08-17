import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19814

open scoped BigOperators Classical

noncomputable section

abbrev Multiplicity (ell N : ℕ) :=
  {t : ℕ →₀ ℕ //
    t.sum (fun _ n => n) = ell ∧
      t.sum (fun j n => j * n) = N}

def monomialProduct (t : ℕ →₀ ℕ) : MvPolynomial (Fin 2) ℚ :=
  t.support.prod (fun j =>
    (1 + MvPolynomial.X (0 : Fin 2) *
      MvPolynomial.X (1 : Fin 2) ^ j) ^ t j)

def D (ell N : ℕ) : ℕ :=
  Module.finrank ℚ
    (Submodule.span ℚ
      (Set.range (fun t : Multiplicity ell N => monomialProduct t.1)))

def U (ell N : ℕ) : ℕ :=
  1 +
      (∑ r ∈ (Finset.Icc 1 (((ell + 1) / 2) - 1)),
        (N + 1 - 2 * r)) +
    if Even ell then
      (N + 2) / 2 - ell / 2
    else 0

def allFactorMonomialSpanFormula_claim19814 : Prop :=
  ∀ ell N : ℕ, 1 ≤ ell → D ell N = U ell N

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19814
