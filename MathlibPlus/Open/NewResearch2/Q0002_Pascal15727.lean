import Mathlib

open scoped BigOperators LaurentPolynomial

namespace MathlibPlus.Open.NewResearch2.Q0002.Pascal15727

noncomputable section

private def pascalKernel (R q s : ℤ) : ℚ :=
  if _h : 0 ≤ R + s - 1 then
    (LaurentPolynomial.C 1 + LaurentPolynomial.C 2 * LaurentPolynomial.T 1) *
        LaurentPolynomial.T s *
      (LaurentPolynomial.C 1 + LaurentPolynomial.T 1) ^
          Int.toNat (R + s - 1) |>.coeff q
  else 0

private def selectedRow (R q s : ℤ) : ℚ :=
  ((R + q : ℤ) : ℚ) * pascalKernel R (q - 1) s - pascalKernel R q s

/-- Claim 15727.  The kernels are Laurent coefficients of the exact Pascal
kernel from Claim 15724, and the selected rows use the exact adjacent formula;
the four base columns are stated on the reachable nonnegative `q` domain. -/
def claim15727 : Prop :=
  (∀ q : ℤ, 0 ≤ q →
    pascalKernel 1 q 0 =
      if q = 0 then 1 else if q = 1 then 2 else 0) ∧
  (∀ q : ℤ, 0 ≤ q →
    selectedRow 1 q 0 =
      if q = 0 then -1 else if q = 1 then 0 else if q = 2 then 6 else 0) ∧
  (∀ q : ℤ, 0 ≤ q →
    pascalKernel 2 q (-1) = if q = 0 then 2 else 0) ∧
  (∀ q : ℤ, 0 ≤ q →
    selectedRow 2 q (-1) =
      if q = 0 then 0 else if q = 1 then 6 else 0)

end
end MathlibPlus.Open.NewResearch2.Q0002.Pascal15727
