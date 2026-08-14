import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.R1519

/-- Invariance in one nonzero direction, scalar-coordinate constancy, and
factorization through the corresponding submodule quotient. -/
def claim38091 : Prop :=
  ∀ (X V : Type*)
    [AddCommGroup X] [AddCommGroup V]
    [Module (ZMod 3) X] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) X] [FiniteDimensional (ZMod 3) V],
    ∀ (e₀ : X), e₀ ≠ 0 →
      ∀ (f : X → V),
        (∀ x : X, f (x + e₀) = f x) →
          let P : Submodule (ZMod 3) X :=
            Submodule.span (ZMod 3) ({e₀} : Set X)
          (∀ (φ : V →ₗ[ZMod 3] ZMod 3) (a : ZMod 3),
              φ (f (a • e₀) - f 0) = 0) ∧
            (∃ g : (X ⧸ P) → V,
              ∀ x : X, f x = g (Submodule.Quotient.mk x)) ∧
            (∀ (ℓ : X →ₗ[ZMod 3] V),
              ℓ e₀ = 0 →
                ∃ L : (X ⧸ P) →ₗ[ZMod 3] V,
                  ∀ x : X, ℓ x = L (Submodule.Quotient.mk x))

end MathlibPlus.Open.LinearAlgebra.R1519
