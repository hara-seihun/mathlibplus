import Mathlib

namespace MathlibPlus.Algebra.Claim31850

/-- The safe derivative edge of three translation charts is the displayed
translation, and source inversion has scalar unit `-1`. -/
theorem safeDerivativeEdge_translation
    {A : Type*} [AddCommGroup A]
    (t_hk t_k t_theta : A) :
    let q_hk : A → A := fun z => z + t_hk
    let q_k_inv : A → A := fun z => z - t_k
    let q_theta_inv : A → A := fun z => z - t_theta
    (∀ z : A, q_hk (q_k_inv (q_theta_inv z)) =
      z + t_hk - t_k - t_theta) ∧
      (∀ z : A, -z = (-1 : ℤ) • z) := by
  dsimp
  constructor
  · intro z
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · intro z
    simp

/-- Translation by `t` has inverse translation by `-t`. -/
theorem translation_inverse
    {A : Type*} [AddCommGroup A] (t : A) :
    Function.LeftInverse (fun z : A => z - t) (fun z => z + t) ∧
      Function.LeftInverse (fun z : A => z + t) (fun z => z - t) := by
  constructor <;> intro z <;> simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

end MathlibPlus.Algebra.Claim31850
