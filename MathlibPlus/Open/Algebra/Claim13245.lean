import Mathlib
import MathlibPlus.Algebra.Claim13230

namespace MathlibPlus.Open.Algebra

noncomputable section

/-- The fixed degree-seven trace example has all the advertised generic
properties, but its lossless integer-symmetric realization does not exist. -/
def claim13245 : Prop :=
  let Q : Polynomial ℤ :=
    Polynomial.X ^ 7 - 8 * Polynomial.X ^ 5 + 19 * Polynomial.X ^ 3 -
      12 * Polynomial.X + 1
  let P : Polynomial ℤ :=
    Polynomial.X ^ 14 - Polynomial.X ^ 12 + Polynomial.X ^ 7 -
      Polynomial.X ^ 2 + 1
  let M : Polynomial ℤ → ℝ := fun p =>
    ((p.map (algebraMap ℤ ℂ)).roots.map (fun z => max (1 : ℝ) ‖z‖)).prod
  let qReal : Polynomial ℝ := Q.map (Int.castRingHom ℝ)
  (Irreducible (Q.map (Int.castRingHom (ZMod 2))) ∧
      Irreducible (Q.map (Int.castRingHom ℚ)) ∧
      qReal.natDegree = 7 ∧
      qReal.Splits ∧
      (∀ x : ℂ, x ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ℂ) x P =
          x ^ 7 * Polynomial.eval₂ (algebraMap ℤ ℂ) (x + x⁻¹) Q) ∧
      (1.2026167436 : ℝ) ≤ M P ∧
      M P < 1.2026167437 ∧
      (1.202 : ℝ) < M P ∧
      M P < 1.203 ∧
      (1.203 : ℝ) < 1.3) ∧
    ¬ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (C : Polynomial ℤ),
      (∀ i j : Fin n, A i j = A j i) ∧
      Matrix.charpoly A = Q * C ∧
      (∀ z : ℂ,
        (C.map (algebraMap ℤ ℂ)).IsRoot z →
          z.im = 0 ∧ (-2 : ℝ) ≤ z.re ∧ z.re ≤ 2)

end

end MathlibPlus.Open.Algebra
