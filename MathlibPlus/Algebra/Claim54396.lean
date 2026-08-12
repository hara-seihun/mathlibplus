import Mathlib

namespace MathlibPlus.Algebra.Claim54396

/-!
Formalization of admitted claim 54396 (R-5431).  The matrix-side statement
keeps the displayed entries and two-sided inverses literal.  The final theorem
then transports those four units through the stated unital ring equivalence.
-/

private def U₁ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![X 0 0, 1; 1, 0]
private def V₁ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, X 0 0]
private def U₂ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, X 1 1]
private def V₂ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![X 1 1, 1; 1, 0]
private def U₃ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, X 0 1; 0, 1]
private def V₃ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R := U₃ X
private def U₄ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; X 1 0, 1]
private def V₄ {R : Type*} [Ring R]
    (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R := U₄ X

variable {R : Type*} [Ring R] [CharP R 2]

private lemma inv_identities (X : Matrix (Fin 2) (Fin 2) R) :
    U₁ X * V₁ X = 1 ∧ V₁ X * U₁ X = 1 ∧
    U₂ X * V₂ X = 1 ∧ V₂ X * U₂ X = 1 ∧
    U₃ X * V₃ X = 1 ∧ V₃ X * U₃ X = 1 ∧
    U₄ X * V₄ X = 1 ∧ V₄ X * U₄ X = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₁, V₁, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₁, V₁, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₂, V₂, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₂, V₂, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₃, V₃, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₃, V₃, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₄, V₄, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U₄, V₄, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private lemma sum_identity (X : Matrix (Fin 2) (Fin 2) R) :
    X = U₁ X + U₂ X + U₃ X + U₄ X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U₁, U₂, U₃, U₄, Matrix.add_apply]
  all_goals
    first
    | exact CharTwo.add_self_eq_zero 1
    | (conv_rhs => rw [add_assoc]; simp [CharTwo.add_self_eq_zero])

/-- The four displayed matrices and their displayed two-sided inverses
reconstruct every matrix in characteristic two. -/
theorem matrix_four_unit_decomposition_claim54396
    (X : Matrix (Fin 2) (Fin 2) R) :
    U₁ X * V₁ X = 1 ∧ V₁ X * U₁ X = 1 ∧
    U₂ X * V₂ X = 1 ∧ V₂ X * U₂ X = 1 ∧
    U₃ X * V₃ X = 1 ∧ V₃ X * U₃ X = 1 ∧
    U₄ X * V₄ X = 1 ∧ V₄ X * U₄ X = 1 ∧
    X = U₁ X + U₂ X + U₃ X + U₄ X := by
  exact ⟨(inv_identities X).1, (inv_identities X).2.1,
    (inv_identities X).2.2.1, (inv_identities X).2.2.2.1,
    (inv_identities X).2.2.2.2.1, (inv_identities X).2.2.2.2.2.1,
    (inv_identities X).2.2.2.2.2.2.1, (inv_identities X).2.2.2.2.2.2.2,
    sum_identity X⟩

private def pullbackUnit {A : Type*} [Ring A]
    (e : A ≃+* Matrix (Fin 2) (Fin 2) A)
    {X Y : Matrix (Fin 2) (Fin 2) A} (hXY : X * Y = 1) (hYX : Y * X = 1) : Aˣ :=
  Units.mk (e.symm X) (e.symm Y)
    (by simpa using congrArg e.symm hXY)
    (by simpa using congrArg e.symm hYX)

/-- A unital characteristic-two ring self-isomorphic to its two-by-two matrix
ring has every element as a sum of four units. -/
theorem every_element_sum_four_units_claim54396
    {A : Type*} [Ring A] [CharP A 2]
    (e : A ≃+* Matrix (Fin 2) (Fin 2) A) (a : A) :
    ∃ u₁ u₂ u₃ u₄ : Aˣ, a = u₁ + u₂ + u₃ + u₄ := by
  let X : Matrix (Fin 2) (Fin 2) A := e a
  rcases matrix_four_unit_decomposition_claim54396 X with
    ⟨h₁, h₁', h₂, h₂', h₃, h₃', h₄, h₄', hsum⟩
  let u₁ : Aˣ := pullbackUnit e h₁ h₁'
  let u₂ : Aˣ := pullbackUnit e h₂ h₂'
  let u₃ : Aˣ := pullbackUnit e h₃ h₃'
  let u₄ : Aˣ := pullbackUnit e h₄ h₄'
  refine ⟨u₁, u₂, u₃, u₄, ?_⟩
  have hu₁ : e (u₁ : A) = U₁ X := by
    simp [u₁, pullbackUnit]
  have hu₂ : e (u₂ : A) = U₂ X := by
    simp [u₂, pullbackUnit]
  have hu₃ : e (u₃ : A) = U₃ X := by
    simp [u₃, pullbackUnit]
  have hu₄ : e (u₄ : A) = U₄ X := by
    simp [u₄, pullbackUnit]
  apply e.injective
  calc
    e a = X := by rfl
    _ = U₁ X + U₂ X + U₃ X + U₄ X := hsum
    _ = e (u₁ : A) + e (u₂ : A) + e (u₃ : A) + e (u₄ : A) := by
      rw [hu₁, hu₂, hu₃, hu₄]
    _ = e ((u₁ : A) + (u₂ : A) + (u₃ : A) + (u₄ : A)) := by
      simp only [map_add]

end MathlibPlus.Algebra.Claim54396
