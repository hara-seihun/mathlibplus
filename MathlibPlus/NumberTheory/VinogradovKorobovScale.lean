import Mathlib

namespace MathlibPlus.NumberTheory.VinogradovKorobovScale

/--
The Vinogradov--Korobov scale on the explicit positive-height domain `t > 1`.
The real powers use Mathlib's `Real.rpow` convention.
-/
noncomputable def scale (t : {t : ℝ // 1 < t}) : ℝ :=
  Real.rpow (Real.log (t : ℝ)) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log (t : ℝ))) (1 / 3 : ℝ)

end MathlibPlus.NumberTheory.VinogradovKorobovScale
