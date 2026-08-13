import Mathlib

namespace MathlibPlus.Algebra.AffineFiber

/-- An affine map on a prime cyclic fibre over a base permutation, as in claim 6053. -/
noncomputable def affineFiberEquiv_claim6053
    (p : ℕ) (_hp : Nat.Prime p) {B : Type*}
    (e : (ZMod p)ˣ) (ell : B → ZMod p) (qbar : B ≃ B) :
    (ZMod p × B) ≃ (ZMod p × B) :=
  { toFun := fun z => (e.val * z.1 + ell z.2, qbar z.2)
    invFun := fun z =>
      ((↑(e⁻¹) * (z.1 - ell (qbar.symm z.2))), qbar.symm z.2)
    left_inv := by
      intro z
      rcases z with ⟨z, b⟩
      ext
      · simp [add_assoc, sub_eq_add_neg]
      · simp
    right_inv := by
      intro z
      rcases z with ⟨z, b⟩
      ext
      · simp [add_assoc, sub_eq_add_neg]
      · simp }

end MathlibPlus.Algebra.AffineFiber
