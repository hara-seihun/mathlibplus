import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 19222: reciprocal-series Hankel determinant identity.  The inverse
series is represented by an explicit two-sided inverse `B`; the coefficient
ring is quantified as a field so the displayed power of `h₀` is literal. -/
def reciprocalSeriesDeterminant_claim19222 : Prop :=
  ∀ (K : Type*) [Field K] (H B : PowerSeries K),
    PowerSeries.constantCoeff H ≠ 0 → H * B = 1 →
    ∀ N : ℕ,
      Matrix.det (fun i j : Fin N =>
        PowerSeries.coeff (i.val + j.val + 1) B) =
        (-1 : K) ^ N *
          (PowerSeries.constantCoeff H)⁻¹ ^ (2 * N) *
          Matrix.det (fun i j : Fin N =>
            PowerSeries.coeff (i.val + j.val + 1) H)

end MathlibPlus.Open.Algebra
