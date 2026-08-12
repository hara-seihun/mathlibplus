import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The order-five centered derivative determinant from the admitted claim.  The
right-hand determinant is the Wronskian of the five functions
`f, f', f'', f''', f''''`, written with the polynomial derivative and its
iterates so that the convention is explicit and does not depend on a named
Wronskian API.
-/
def centeredOrderFiveDerivativeDeterminant_claim845 : Prop :=
  ∀ (f : Polynomial ℝ) (x : ℝ),
    Matrix.det (fun i j : Fin 5 =>
      ((Polynomial.derivative^[i.val + j.val]) f).eval x) =
      Matrix.det (fun i j : Fin 5 =>
        ((Polynomial.derivative^[i.val])
          ((Polynomial.derivative^[j.val]) f)).eval x)

end MathlibPlus.Open.Analysis
