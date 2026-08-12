import MathlibPlus.Basic

namespace MathlibPlus.Algebra.CoordinateCongruence

/-!
Formalization of admitted claim 28976.  The source's polynomial congruence is
represented coefficientwise for integer polynomials, and its scalar congruence
hypothesis is `Int.ModEq`.
-/

/-- Congruent scalar coordinates give coefficientwise-congruent affine shifts. -/
theorem coefficient_congruence_claim28976
    (Q₀ D Qᵢ Qⱼ : Polynomial ℤ) (cᵢ cⱼ q : ℤ)
    (hᵢ : Qᵢ = Q₀ + Polynomial.C cᵢ * D)
    (hⱼ : Qⱼ = Q₀ + Polynomial.C cⱼ * D)
    (hmod : cᵢ ≡ cⱼ [ZMOD q]) :
    ∀ n : ℕ, Qᵢ.coeff n ≡ Qⱼ.coeff n [ZMOD q] := by
  intro n
  rw [hᵢ, hⱼ, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  exact Int.ModEq.add (Int.ModEq.refl _) (Int.ModEq.mul_right _ hmod)

end MathlibPlus.Algebra.CoordinateCongruence
