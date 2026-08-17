import MathlibPlus.Algebra.FactorialTransform

namespace MathlibPlus.Open.ResearchFormalization.R0860Claim25377

noncomputable section

open scoped BigOperators
open MathlibPlus.Algebra.FactorialTransform

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Coefficientwise multiplication by the multi-index factorial, the inverse
    normalization to the reviewed factorial transform. -/
noncomputable def factorialTransformInv {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  Finsupp.sum (AddMonoidAlgebra.coeff p)
    (fun a c =>
      MvPolynomial.C (c * factorialWeight a) *
        MvPolynomial.monomial a 1)

/-- The shifted edge-lengthening operator in a chosen variable. -/
noncomputable def shiftedLengthening {σ : Type*} [DecidableEq σ]
    (x : σ) (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  Finsupp.sum (AddMonoidAlgebra.coeff p)
    (fun a c =>
      if h : a x = 0 then 0
      else MvPolynomial.monomial (a - Finsupp.single x 1) c)

/-- Formal partial differentiation in a chosen variable on the same concrete
    finite-support multivariate polynomial carrier. -/
noncomputable def partialDerivative {σ : Type*} [DecidableEq σ]
    (x : σ) (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  Finsupp.sum (AddMonoidAlgebra.coeff p)
    (fun a c =>
      if h : a x = 0 then 0
      else
        MvPolynomial.C (c * (a x : ℚ)) *
          MvPolynomial.monomial (a - Finsupp.single x 1) 1)

/-- Claim 25377: the exact coefficientwise factorial normalization sends the
    shifted lengthening conjugate to the formal partial derivative, in every
    variable. -/
def claim25377_factorialTransformConjugatesLengthening : Prop :=
  ∀ {σ : Type*} [DecidableEq σ] (x : σ) (p : MvPolynomial σ ℚ),
    factorialTransform
        (shiftedLengthening x (factorialTransformInv p)) =
      partialDerivative x p

end

end MathlibPlus.Open.ResearchFormalization.R0860Claim25377
