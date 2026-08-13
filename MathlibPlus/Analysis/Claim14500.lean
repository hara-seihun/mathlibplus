import Mathlib

namespace MathlibPlus.Analysis.Claim14500

/-- Vandermonde locking for the toy hyperbolic-sine system.  The finite index
`Fin m` is exactly the range `0, ..., m - 1` of moment equations. -/
theorem locking_claim14500
    {m : ℕ} (freq theta : Fin m → ℝ) (k : ℝ)
    (hk : k ≠ 0) (hfreqinj : Function.Injective freq)
    (hfreqnz : ∀ j, freq j ≠ 0)
    (hzero : ∀ q : Fin m,
      ∑ j : Fin m, Real.sinh (k * freq j * theta j) * freq j ^ (q : ℕ) = 0) :
    ∀ j, theta j = 0 := by
  have hb : (fun j : Fin m => Real.sinh (k * freq j * theta j)) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hfreqinj hzero
  intro j
  have hs : Real.sinh (k * freq j * theta j) = 0 := congrFun hb j
  have harg : k * freq j * theta j = 0 := Real.sinh_eq_zero.mp hs
  have hkl : k * freq j ≠ 0 := mul_ne_zero hk (hfreqnz j)
  exact (mul_eq_zero.mp harg).resolve_left hkl

end MathlibPlus.Analysis.Claim14500
