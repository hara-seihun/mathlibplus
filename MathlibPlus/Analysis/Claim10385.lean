import Mathlib

namespace MathlibPlus.Analysis.Claim10385

/-!
Claim 10385 is recorded at the algebraic Cartan-identity interface because the
source does not specify a manifold or a concrete differential-form bundle.
The two contraction maps have the degree-shifted types needed for
`ι_X (d u)` and `ι_X u`; no horizontal or resonance hypothesis is weakened.
-/

/-- A nonzero resonant horizontal form has a non-horizontal differential. -/
theorem horizontal_resonance_not_subcomplex_claim10385
    {Eprev E F : Type*}
    [AddCommGroup Eprev] [Module ℂ Eprev]
    [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (ι₀ : E →ₗ[ℂ] Eprev) (ι₁ : F →ₗ[ℂ] E)
    (dPrev : Eprev →ₗ[ℂ] E) (d : E →ₗ[ℂ] F) (L : E →ₗ[ℂ] E)
    (u : E) (spectralValue : ℂ)
    (hCartan : ι₁ (d u) = L u - dPrev (ι₀ u))
    (horiz : ι₀ u = 0)
    (resonance : L u = spectralValue • u)
    (hSpectralValue : spectralValue ≠ 0) (hu : u ≠ 0) :
    ι₁ (d u) ≠ 0 := by
  rw [hCartan, horiz, map_zero, sub_zero, resonance]
  intro hzero
  rcases smul_eq_zero.mp hzero with hscalar | hu'
  · exact hSpectralValue hscalar
  · exact hu hu'

end MathlibPlus.Analysis.Claim10385
