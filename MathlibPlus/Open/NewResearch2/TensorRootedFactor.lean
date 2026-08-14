import Mathlib

namespace MathlibPlus.Open.NewResearch2.TensorRootedFactor

/-- The scalar rooted-factor carrier is represented by its unital subalgebra
inside the countable multivariate polynomial ring; the conclusion keeps both
an explicit separated-variable algebra embedding and the no-zero-divisor
property of the tensor product. -/
def claim26266 : Prop :=
  ∀ (A_F : Subalgebra ℚ (MvPolynomial (Option ℕ) ℚ)),
    ∃ e :
        (TensorProduct ℚ (↥A_F) (↥A_F)) →ₐ[ℚ]
          MvPolynomial (Option ℕ ⊕ Option ℕ) ℚ,
      Function.Injective e ∧
      (0 : TensorProduct ℚ (↥A_F) (↥A_F)) ≠ 1 ∧
      (∀ x y : TensorProduct ℚ (↥A_F) (↥A_F),
        x * y = 0 → x = 0 ∨ y = 0)

end MathlibPlus.Open.NewResearch2.TensorRootedFactor
