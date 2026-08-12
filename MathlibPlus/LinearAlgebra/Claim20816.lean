import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim20816

open Matrix

/-- Every integral elementary row transvection has determinant one. -/
theorem elementary_row_transvection_det_claim20816
    {n : Type*} [DecidableEq n] [Fintype n]
    (i j : n) (hij : i ≠ j) (a : ℤ) :
    (Matrix.transvection i j a).det = 1 :=
  Matrix.det_transvection_of_ne i j hij a

/-- An ordered finite product of elementary transvections remains in the
special-linear determinant-one locus. -/
theorem product_transvection_det_claim20816
    {ι n : Type*} [DecidableEq n] [Fintype n]
    (l : List ι) (i j : ι → n) (a : ι → ℤ)
    (hij : ∀ k ∈ l, i k ≠ j k) :
    ((l.map (fun k => Matrix.transvection (i k) (j k) (a k))).prod).det = 1 := by
  induction l with
  | nil => simp
  | cons k l ih =>
      rw [List.map_cons, List.prod_cons, Matrix.det_mul,
        Matrix.det_transvection_of_ne (i k) (j k) (hij k (by simp))]
      simp [ih (fun x hx => hij x (by simp [hx]))]

/-- In particular the recorded product indexed by `Fin 16` has determinant one
over the integral coefficient ring. -/
theorem fin16_product_transvection_det_claim20816
    (i j : Fin 16 → Fin 16) (a : Fin 16 → ℤ)
    (hij : ∀ k, i k ≠ j k) :
    (((List.ofFn (fun k : Fin 16 => k)).map
      (fun k => Matrix.transvection (i k) (j k) (a k))).prod).det = 1 := by
  apply product_transvection_det_claim20816
  intro k hk
  exact hij k

end MathlibPlus.LinearAlgebra.Claim20816
