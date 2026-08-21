import Mathlib

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

/-- Claim 11013: the centered involution `z ↦ -conj z` generates the displayed
four-point quartet from `1 + 2 I`. -/
theorem centeredSpectralQuartet_claim11013 :
    let lam : ℂ := 1 + 2 * Complex.I
    ({lam, -(starRingEnd ℂ) lam, (starRingEnd ℂ) lam, -lam} : Finset ℂ) =
      ({1 + 2 * Complex.I, -1 + 2 * Complex.I,
        1 - 2 * Complex.I, -1 - 2 * Complex.I} : Finset ℂ) := by
  dsimp
  rw [map_add, map_mul, map_ofNat, map_one, Complex.conj_I]
  apply Finset.ext
  intro z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  ring_nf

end MathlibPlus.Complex.QuartetCharacteristicPolynomial
