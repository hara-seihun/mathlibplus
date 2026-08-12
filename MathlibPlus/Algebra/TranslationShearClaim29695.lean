import Mathlib

namespace MathlibPlus.Algebra.Claim29695

/-- The mixed additive/multiplicative product law used by the shear packet. -/
def productMul {A H : Type*} [AddGroup A] [Group H]
    (p q : A × H) : A × H :=
  (p.1 + q.1, p.2 * q.2)

/-- Inverse for the mixed product law. -/
def productInv {A H : Type*} [AddGroup A] [Group H]
    (p : A × H) : A × H :=
  (-p.1, p.2⁻¹)

/-- The shear on the product of the abelian and finite-group factors. -/
def translationShear {A H : Type*} [AddGroup A] [Group H]
    (τ : H → A) : A × H → A × H :=
  fun p => (p.1 + τ p.2, p.2)

/-- The inverse shear used to define the normalized relative derivative. -/
def translationShearInv {A H : Type*} [AddGroup A] [Group H]
    (τ : H → A) : A × H → A × H :=
  fun p => (p.1 - τ p.2, p.2)

/-- The normalized relative derivative of a map `f` in the product law is
`f⁻¹ (f(p * (u,k)) * f(u,k)⁻¹)`, specialized to the translation shear. -/
def normalizedRelativeDerivative {A H : Type*} [AddGroup A] [Group H]
    (τ : H → A) (u : A) (k : H) : A × H → A × H :=
  fun p =>
    translationShearInv τ
      (productMul
        (translationShear τ (productMul p (u, k)))
        (productInv (translationShear τ (u, k))))

/-- Exact application formula for the normalized relative derivative of the
translation shear.  The normalization hypothesis `τ 1 = 0` is retained even
though the displayed application formula does not need to rewrite by it. -/
theorem normalizedRelativeDerivative_apply_claim29695
    {A H : Type*} [Fintype A] [AddCommGroup A] [Fintype H] [Group H]
    (τ : H → A) (hτ : τ 1 = 0) (u : A) (k : H) (a : A) (h : H) :
    normalizedRelativeDerivative τ u k (a, h) =
      (a + τ (h * k) - τ k - τ h, h) := by
  simp [normalizedRelativeDerivative, translationShearInv, productMul,
    productInv, translationShear, hτ]
  abel

end MathlibPlus.Algebra.Claim29695
