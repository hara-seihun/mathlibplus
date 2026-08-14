import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-
The coefficient ring is the polynomial ring in the component variables
x₁, x₂, ...; the natural-number variable `k` represents x_(k+1).
A polynomial has finite support, so its displayed sum is the finite form of
Σ_{k≥0} x_(k+1) p_k(x).
-/
abbrev RootClosureCoefficientRing := MvPolynomial ℕ ℚ

noncomputable def rootClosureComponentVariable (k : ℕ) : RootClosureCoefficientRing :=
  MvPolynomial.X k

noncomputable def scalarRootClosure
    (P : Polynomial RootClosureCoefficientRing) :
    Polynomial RootClosureCoefficientRing :=
  Polynomial.X * P +
    P.support.sum (fun k =>
      Polynomial.C (rootClosureComponentVariable k * P.coeff k))

end MathlibPlus.Open.ResearchFormalization
