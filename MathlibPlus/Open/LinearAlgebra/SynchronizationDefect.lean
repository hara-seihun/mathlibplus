import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

noncomputable section

/-- The rank excess of the paired response over the scalar row. -/
def synchronizationDefect
    {C₀ W₀ Z : Type*}
    [AddCommGroup C₀] [AddCommGroup W₀] [AddCommGroup Z]
    [Module ℚ C₀] [Module ℚ W₀] [Module ℚ Z]
    [FiniteDimensional ℚ C₀] [FiniteDimensional ℚ W₀] [FiniteDimensional ℚ Z]
    (L₀ : C₀ →ₗ[ℚ] W₀) (D : C₀ →ₗ[ℚ] Z) : ℕ :=
  Module.finrank ℚ (LinearMap.range (L₀.prod D)) -
    Module.finrank ℚ (LinearMap.range L₀)

/--
The concrete source-relation and coboundary-witness consequences of a
positive synchronization defect.
-/
def synchronizationDefectCertificate : Prop :=
  ∀
    (C₀ C₁ W₀ W₁ Z : Type*)
    [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup W₀] [AddCommGroup W₁] [AddCommGroup Z]
    [Module ℚ C₀] [Module ℚ C₁]
    [Module ℚ W₀] [Module ℚ W₁] [Module ℚ Z]
    [FiniteDimensional ℚ C₀] [FiniteDimensional ℚ C₁]
    [FiniteDimensional ℚ W₀] [FiniteDimensional ℚ W₁]
    [FiniteDimensional ℚ Z]
    (L₀ : C₀ →ₗ[ℚ] W₀) (L₁ : C₁ →ₗ[ℚ] W₁)
    (A₀ : C₀ →ₗ[ℚ] Z) (A₁ : C₁ →ₗ[ℚ] Z)
    (E : C₀ →ₗ[ℚ] C₁) (S : W₀ →ₗ[ℚ] W₁)
    (_compatibility : L₁.comp E = S.comp L₀),
    let D_E : C₀ →ₗ[ℚ] Z := A₁.comp E - A₀
    let σ : ℕ := synchronizationDefect L₀ D_E
    (σ > 0 →
      ∃ r : C₀, r ∈ LinearMap.ker L₀ ∧ D_E r ≠ 0) ∧
    ((∀ r : C₀, r ∈ LinearMap.ker L₀ → D_E r = 0) →
      ∃ Ψ : W₀ →ₗ[ℚ] Z, D_E = Ψ.comp L₀)

end
end MathlibPlus.Open.LinearAlgebra
