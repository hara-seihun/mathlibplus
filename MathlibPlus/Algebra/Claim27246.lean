import Mathlib

namespace MathlibPlus.Algebra.Claim27246

/-!
The component interpolation is a cubic polynomial in a rational parameter.
The augmented connected-profile map is represented by a rational linear map,
and “the first connected-profile row is affine-linear” by `a + s • b`.
-/

/-- An affine image of a cubic interpolation has zero quadratic and cubic
profile coefficients. -/
theorem cubicProfileKernel
    {n m : ℕ}
    (e₀ d r w : Fin n → ℚ)
    (Ψ : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (a b : Fin m → ℚ)
    (hAffine : ∀ s : ℚ,
      Ψ (e₀ + s • d + s ^ 2 • r + s ^ 3 • w) = a + s • b) :
    Ψ r = 0 ∧ Ψ w = 0 := by
  have hcoord : ∀ j : Fin m, Ψ r j = 0 ∧ Ψ w j = 0 := by
    intro j
    have h0 := hAffine 0
    have h1 := hAffine 1
    have hm1 := hAffine (-1)
    have h2 := hAffine 2
    simp only [LinearMap.map_add] at h0 h1 hm1 h2
    simp_rw [LinearMap.map_smul] at h0 h1 hm1 h2
    have h0j := congrFun h0 j
    have h1j := congrFun h1 j
    have hm1j := congrFun hm1 j
    have h2j := congrFun h2 j
    norm_num [Pi.add_apply, Pi.smul_apply] at h0j h1j hm1j h2j
    constructor <;> linarith [h0j, h1j, hm1j, h2j]
  constructor
  · funext j
    exact (hcoord j).1
  · funext j
    exact (hcoord j).2

end MathlibPlus.Algebra.Claim27246
