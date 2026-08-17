import Mathlib

open scoped Polynomial
open Polynomial

namespace MathlibPlus.Open.Algebra.Claim13228HouseBeta

/-- Claim 13228: for the fixed exterior-root product, the largest conjugate
modulus is `a²`, and `house(β) = a² = M(P)`. -/
def claim13228 : Prop :=
  let P : ℤ[X] :=
    X ^ 6 + C (2 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 3 +
      C (2 : ℤ) * X ^ 2 + C (1 : ℤ)
  let Pℚ : ℚ[X] := P.map (Int.castRingHom ℚ)
  let Pℂ : ℂ[X] := Pℚ.map (algebraMap ℚ ℂ)
  (Pℚ.Monic ∧ Pℚ.natDegree = 6 ∧ Pℚ.coeff 0 = 1 ∧
      Pℚ.reverse = Pℚ ∧ Irreducible Pℚ) ∧
    ∃ a : ℝ, 1 < a ∧
      ∃ r : Fin 6 → ℂ,
        ((Finset.univ : Finset (Fin 6)).1.map r = Pℂ.roots) ∧
          ‖r 0‖ = a ∧ ‖r 1‖ = a ∧
            ‖r 2‖ = a⁻¹ ∧ ‖r 3‖ = a⁻¹ ∧
              ‖r 4‖ = (1 : ℝ) ∧ ‖r 5‖ = (1 : ℝ) ∧
                let β : ℂ := r 0 * r 1
                let F : ℚ[X] := minpoly ℚ β
                let Fℂ : ℂ[X] := F.map (algebraMap ℚ ℂ)
                let M_P : ℝ := Polynomial.mahlerMeasure Pℂ
                let house_β : ℝ :=
                  sSup {u : ℝ | ∃ z : ℂ, z ∈ Fℂ.roots ∧ u = ‖z‖}
                Irreducible F ∧ F.natDegree = 12 ∧
                  (∀ z : ℂ, z ∈ Fℂ.roots → ‖z‖ ≤ a ^ 2) ∧
                  (∃ z : ℂ, z ∈ Fℂ.roots ∧ ‖z‖ = a ^ 2) ∧
                  house_β = a ^ 2 ∧ a ^ 2 = M_P

end MathlibPlus.Open.Algebra.Claim13228HouseBeta
