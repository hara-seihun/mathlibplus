import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

namespace MathlibPlus.Complex.QuartetCharacteristicPolynomial

/-- Claim 11014: the witness quartet at `λ = 1 + 2 I` has characteristic
polynomial `z^4 + 6 z^2 + 25`. -/
theorem quartetCharacteristicPolynomial (z : ℂ) :
    let lam : ℂ := 1 + 2 * Complex.I
    (z - lam) * (z + (starRingEnd ℂ) lam) *
        (z - (starRingEnd ℂ) lam) * (z + lam) =
      z ^ 4 + 6 * z ^ 2 + 25 := by
  dsimp
  rw [map_add, map_mul, map_ofNat, map_one, Complex.conj_I]
  ring_nf
  simp
  ring

end MathlibPlus.Complex.QuartetCharacteristicPolynomial
