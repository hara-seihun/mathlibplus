import Mathlib

open scoped BigOperators Polynomial
open Polynomial

namespace MathlibPlus.Open.Algebra

namespace Claim13217

def irreducibility : Prop :=
  let P : ℤ[X] :=
    X ^ 6 + C (2 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 3 +
      C (2 : ℤ) * X ^ 2 + C (1 : ℤ)
  let P₂ : (ZMod 2)[X] := P.map (Int.castRingHom (ZMod 2))
  let Pℚ : ℚ[X] := P.map (Int.castRingHom ℚ)
  P₂ = X ^ 6 + X ^ 3 + C (1 : ZMod 2) ∧
    Irreducible P₂ ∧ Irreducible Pℚ

end Claim13217

namespace Claim13219

def rootModulusLedger : Prop :=
  let P : ℤ[X] :=
    X ^ 6 + C (2 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 3 +
      C (2 : ℤ) * X ^ 2 + C (1 : ℤ)
  let Pℚ : ℚ[X] := P.map (Int.castRingHom ℚ)
  let Pℂ : ℂ[X] := Pℚ.map (algebraMap ℚ ℂ)
  ∃ a : ℝ, 1 < a ∧
    Pℂ.roots.map (fun z : ℂ => ‖z‖) =
      ({a, a, a⁻¹, a⁻¹, (1 : ℝ), 1} : Multiset ℝ)

end Claim13219

namespace Claim13226

def reciprocalPairsAndExteriorOrbit : Prop :=
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
              let β : ℂ := r 0 * r 1
              let F : ℚ[X] := minpoly ℚ β
              let allPairs : Finset (Fin 6 × Fin 6) :=
                (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2)
              let reciprocalPairs : Finset (Fin 6 × Fin 6) :=
                allPairs.filter (fun p => r p.1 * r p.2 = 1)
              let pairProducts : Multiset ℂ :=
                allPairs.1.map (fun p => r p.1 * r p.2)
              let secondCompound : ℂ[X] :=
                Finset.prod allPairs (fun p => X - C (r p.1 * r p.2))
              Irreducible F ∧ F.natDegree = 12 ∧
                reciprocalPairs.card = 3 ∧
                  pairProducts =
                    ({(1 : ℂ), 1, 1} : Multiset ℂ) +
                      (F.map (algebraMap ℚ ℂ)).roots ∧
                    secondCompound =
                      (X - C (1 : ℂ)) ^ 3 * F.map (algebraMap ℚ ℂ)

end Claim13226

namespace Claim13229

def houseMahlerMeasure : Prop :=
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
                letI : DecidableEq ℂ := Classical.decEq ℂ
                let M_P : ℝ := Polynomial.mahlerMeasure Pℂ
                let M_F : ℝ := Polynomial.mahlerMeasure Fℂ
                let house_β : ℝ :=
                  sSup (↑(Fℂ.roots.toFinset.image (fun z : ℂ => ‖z‖)) : Set ℝ)
                Irreducible F ∧ F.natDegree = 12 ∧
                  house_β = M_P ∧ M_F = M_P ^ 3 ∧
                    M_P ^ 3 ≠ M_P ∧ M_F ≠ M_P ∧ M_P > 1

end Claim13229

end MathlibPlus.Open.Algebra
