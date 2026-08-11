import Mathlib

namespace MathlibPlus.Open.Algebra

/-!
Statement-fidelity formalization of admitted claim 18297.  The claim's shifted
Hankel matrix `H_N^(1)` is made explicit as the `Fin N` matrix whose `(i,j)`
entry is the coefficient of degree `i+j+1`.  The ambient coefficient object is
an arbitrary field; invertibility is the displayed nonzero constant-coefficient
condition.
-/

/-- Reciprocal shifted-Hankel determinant identity for an invertible formal series. -/
def reciprocalShiftedHankelDeterminantIdentity : Prop :=
  ∀ (R : Type*) [Field R] (N : ℕ) (H : PowerSeries R),
    PowerSeries.coeff 0 H ≠ 0 →
      let shiftedHankel : PowerSeries R → Matrix (Fin N) (Fin N) R :=
        fun F i j => PowerSeries.coeff (i.1 + j.1 + 1) F
      Matrix.det (shiftedHankel H⁻¹) =
        (-1 : R) ^ N * (PowerSeries.coeff 0 H)⁻¹ ^ (2 * N) *
          Matrix.det (shiftedHankel H)

end MathlibPlus.Open.Algebra
