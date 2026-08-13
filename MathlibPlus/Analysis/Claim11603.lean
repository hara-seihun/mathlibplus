import Mathlib

namespace MathlibPlus.Analysis.Claim11603

/-- On the polynomial test domain, the formal adjoint factorization
`A₊ A₋ = A₋* A₋` expands as `(D²+c)²-D²`, with
`c = x² + 1/4`.  The two factors are written as local functions so that no
source-specific differential-operator convention is silently introduced. -/
theorem positiveRadialSquare (x : ℝ) (p : Polynomial ℝ) :
    let Aminus : Polynomial ℝ → Polynomial ℝ := fun q =>
      q.derivative.derivative - q.derivative + Polynomial.C (x ^ 2 + (1 : ℝ) / 4) * q
    let Aplus : Polynomial ℝ → Polynomial ℝ := fun q =>
      q.derivative.derivative + q.derivative + Polynomial.C (x ^ 2 + (1 : ℝ) / 4) * q
    Aplus (Aminus p) =
      p.derivative.derivative.derivative.derivative +
        (2 * Polynomial.C (x ^ 2 + (1 : ℝ) / 4) - 1) *
          p.derivative.derivative +
        (Polynomial.C (x ^ 2 + (1 : ℝ) / 4) *
          Polynomial.C (x ^ 2 + (1 : ℝ) / 4)) * p := by
  dsimp
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C]
  simp
  ring

end MathlibPlus.Analysis.Claim11603
