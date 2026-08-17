import Mathlib

open scoped BigOperators Polynomial
open Polynomial

namespace MathlibPlus.Open.Algebra.Claim13225PairProductModuli

/-- Claim 13225: the fifteen unordered pair products of the fixed six roots
have modulus multiplicities `a²:1`, `a:4`, `1:5`, `a⁻¹:4`, and `a⁻²:1`. -/
def claim13225 : Prop :=
  let P : ℤ[X] :=
    X ^ 6 + C (2 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 3 +
      C (2 : ℤ) * X ^ 2 + C (1 : ℤ)
  let Pℚ : ℚ[X] := P.map (Int.castRingHom ℚ)
  let Pℂ : ℂ[X] := Pℚ.map (algebraMap ℚ ℂ)
  ∃ a : ℝ, 1 < a ∧
    ∃ r : Fin 6 → ℂ,
      ((Finset.univ : Finset (Fin 6)).1.map r = Pℂ.roots) ∧
        ‖r 0‖ = a ∧ ‖r 1‖ = a ∧
          ‖r 2‖ = a⁻¹ ∧ ‖r 3‖ = a⁻¹ ∧
            ‖r 4‖ = (1 : ℝ) ∧ ‖r 5‖ = (1 : ℝ) ∧
              let allPairs : Finset (Fin 6 × Fin 6) :=
                (Finset.univ.product Finset.univ).filter
                  (fun p => p.1 < p.2)
              let pairProducts : Multiset ℂ :=
                allPairs.1.map (fun p => r p.1 * r p.2)
              pairProducts.map (fun z : ℂ => ‖z‖) =
                ({a ^ 2} : Multiset ℝ) +
                  ({a, a, a, a} : Multiset ℝ) +
                    ({(1 : ℝ), 1, 1, 1, 1} : Multiset ℝ) +
                      ({a⁻¹, a⁻¹, a⁻¹, a⁻¹} : Multiset ℝ) +
                        ({(a⁻¹) ^ 2} : Multiset ℝ)

end MathlibPlus.Open.Algebra.Claim13225PairProductModuli
