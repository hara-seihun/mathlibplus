import Mathlib

open scoped BigOperators Polynomial
open Polynomial

namespace MathlibPlus.Open.Algebra.Claim13224

/-- The exterior-root product of the fixed reciprocal polynomial is the
maximal-modulus second-compound eigenvalue, and its minimal polynomial is the
fixed irreducible polynomial of degree twelve. -/
def claim13224 : Prop :=
  let P : ℤ[X] :=
    X ^ 6 + C (2 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 3 +
      C (2 : ℤ) * X ^ 2 + C (1 : ℤ)
  let Pℚ : ℚ[X] := P.map (Int.castRingHom ℚ)
  let Pℂ : ℂ[X] := Pℚ.map (algebraMap ℚ ℂ)
  let F₀ : ℚ[X] :=
    X ^ 12 + X ^ 11 - C (2 : ℚ) * X ^ 10 - C (2 : ℚ) * X ^ 9 +
      X ^ 8 - C (5 : ℚ) * X ^ 7 - C (11 : ℚ) * X ^ 6 -
      C (5 : ℚ) * X ^ 5 + X ^ 4 - C (2 : ℚ) * X ^ 3 -
      C (2 : ℚ) * X ^ 2 + X + C (1 : ℚ)
  ∃ a : ℝ, 1 < a ∧
    ∃ r : Fin 6 → ℂ,
      ((Finset.univ : Finset (Fin 6)).1.map r = Pℂ.roots) ∧
        ‖r 0‖ = a ∧ ‖r 1‖ = a ∧
          ‖r 2‖ = a⁻¹ ∧ ‖r 3‖ = a⁻¹ ∧
            ‖r 4‖ = (1 : ℝ) ∧ ‖r 5‖ = (1 : ℝ) ∧
              let β : ℂ := r 0 * r 1
              let F : ℚ[X] := minpoly ℚ β
              let allPairs : Finset (Fin 6 × Fin 6) :=
                (Finset.univ.product Finset.univ).filter
                  (fun p => p.1 < p.2)
              let pairProducts : Multiset ℂ :=
                allPairs.1.map (fun p => r p.1 * r p.2)
              Irreducible F ∧ F.natDegree = 12 ∧
                F = F₀ ∧
                β ∈ pairProducts ∧
                ∀ p ∈ allPairs, ‖r p.1 * r p.2‖ ≤ ‖β‖

end MathlibPlus.Open.Algebra.Claim13224
