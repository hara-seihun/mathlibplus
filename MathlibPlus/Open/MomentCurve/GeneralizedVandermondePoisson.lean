import Mathlib

namespace MathlibPlus.Open.MomentCurve

/--
Generalized Vandermonde Poisson determinant positivity (claim 19528).
For positive strictly increasing nodes and strictly increasing natural
exponents, the factorial-normalized generalized Vandermonde determinant is
positive.
-/
def generalizedVandermondePoissonDeterminantPositive : Prop :=
  ∀ (d : ℕ) (q : Fin d → ℝ) (m : Fin d → ℕ),
    (∀ i, 0 < q i) →
      StrictMono q →
        StrictMono m →
          0 < Matrix.det (fun i k : Fin d =>
            q i ^ m k / ((m k).factorial : ℝ))

end MathlibPlus.Open.MomentCurve
