import Mathlib

open MvPolynomial

namespace MathlibPlus.Algebra

/-! The displayed `P₃` endpoint primitive and `J` from admitted claim 40766,
written as multivariate integer polynomials in `x₁,…,x₄`. -/

/-- The endpoint primitive `U_{P3}` does not divide the displayed endpoint
polynomial `J`.  The variables are represented by `Fin 5`, with the unused
zero-indexed variable making the source indices `x₁,…,x₄` literal. -/
theorem claim40766_p3_not_dvd_endpoint
    : ¬ (X (3 : Fin 5) + 2 * X (1 : Fin 5) * X (2 : Fin 5) + X (1 : Fin 5) ^ 3 :
        MvPolynomial (Fin 5) ℤ) ∣
      (X (1 : Fin 5) ^ 2 * X (3 : Fin 5) + X (1 : Fin 5) * X (4 : Fin 5) -
        X (1 : Fin 5) * X (2 : Fin 5) ^ 2 - X (2 : Fin 5) * X (3 : Fin 5) :
        MvPolynomial (Fin 5) ℤ) := by
  intro h
  let g : Fin 5 → ℤ := fun i => if i = 1 then 1 else if i = 3 then -1 else 0
  let e := eval₂Hom (RingHom.id ℤ) g
  have hd := map_dvd e h
  have hzero : e (X (3 : Fin 5) + 2 * X (1 : Fin 5) * X (2 : Fin 5) + X (1 : Fin 5) ^ 3) = 0 := by
    simp [e, g]
  have hneg : e (X (1 : Fin 5) ^ 2 * X (3 : Fin 5) + X (1 : Fin 5) * X (4 : Fin 5) -
      X (1 : Fin 5) * X (2 : Fin 5) ^ 2 - X (2 : Fin 5) * X (3 : Fin 5)) = -1 := by
    simp [e, g]
  rw [hzero, hneg] at hd
  norm_num at hd

end MathlibPlus.Algebra
