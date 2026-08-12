import Mathlib

namespace MathlibPlus.Analysis.Claim22040

/--
The exact second-derivative cross-block identity from claim 22040.  The source's
`ω` is used only through its unit-circle relation, recorded explicitly here.
-/
theorem secondDerivativeCrossBlock (T Tdd ω : ℂ)
    (hω : ω * (starRingEnd ℂ) ω = 1) :
    -((T * (starRingEnd ℂ) Tdd).re) - ((ω ^ 2 * T * Tdd).re) =
      -2 * (ω * T).re * (ω * Tdd).re := by
  have hprod₁ : (ω * T) * (starRingEnd ℂ) (ω * Tdd) =
      T * (starRingEnd ℂ) Tdd := by
    calc
      (ω * T) * (starRingEnd ℂ) (ω * Tdd) =
          (ω * (starRingEnd ℂ) ω) * (T * (starRingEnd ℂ) Tdd) := by
            rw [map_mul]
            ring
      _ = T * (starRingEnd ℂ) Tdd := by rw [hω, one_mul]
  have hprod₂ : (ω * T) * (ω * Tdd) = ω ^ 2 * T * Tdd := by
    ring
  have htwice :
      2 * (ω * T).re * (ω * Tdd).re =
        ((ω * T) * (ω * Tdd)).re +
          ((ω * T) * (starRingEnd ℂ) (ω * Tdd)).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hprod₂, hprod₁] at htwice
  linarith

end MathlibPlus.Analysis.Claim22040
