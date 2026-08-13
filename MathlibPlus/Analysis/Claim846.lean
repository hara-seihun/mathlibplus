import Mathlib

namespace MathlibPlus.Analysis

/-- The product polynomial `G(z) = ∏ (1 + α_ν z)` from admitted claim 846.
The coefficient family uses `Fin N`, so its zero-based indices represent the
source's one-based product indices. -/
noncomputable def productFormPolynomial_claim846 {R : Type*} [CommRing R]
    (N : ℕ) (α : Fin N → R) : Polynomial R :=
  ∏ ν : Fin N, (1 + Polynomial.C (α ν) * Polynomial.X)

/-- Evaluation at zero of an iterated polynomial derivative, with the negative
orders in the source convention interpreted as zero. -/
noncomputable def derivativeAtZero_claim846 {R : Type*} [CommRing R]
    (G : Polynomial R) (n : ℤ) : R :=
  if 0 ≤ n then
    ((Polynomial.derivative^[n.toNat]) G).eval 0
  else 0

/-- The order-five determinant `D₅(G)` from claim 846. -/
noncomputable def productFormDerivativeDeterminant5_claim846
    {R : Type*} [CommRing R] (G : Polynomial R) : R :=
  Matrix.det (fun i j : Fin 5 =>
    derivativeAtZero_claim846 G (4 + (j : ℤ) - (i : ℤ)))

end MathlibPlus.Analysis
