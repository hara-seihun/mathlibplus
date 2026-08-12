import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 6192.  The endpoint path series is the all-one formal power series,
and the endpoint decomposition is the exact equation `(1 - X) * H = 1`.
The equation form is used instead of an independently supplied inverse.
-/
theorem endpointDecompositionPathSeries_claim6192 :
    let X : PowerSeries ℚ := PowerSeries.X
    let H : PowerSeries ℚ := PowerSeries.mk 1
    (1 - X) * H = 1 := by
  dsimp
  simpa [mul_comm] using PowerSeries.mk_one_mul_one_sub_eq_one ℚ

end MathlibPlus.Algebra
