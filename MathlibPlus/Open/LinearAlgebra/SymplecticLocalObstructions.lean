import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/-- A nondegenerate alternating bilinear form has even dimension, and a
nonzero space carrying one has dimension at least two. -/
def nondegenerateAlternatingSpacesHaveEvenDimension : Prop :=
  ∀ (𝕜 : Type*) [Field 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V]
    (B : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜),
    (∀ v, B v v = 0) →
    (∀ v, (∀ w, B v w = 0) → v = 0) →
    (∀ w, (∀ v, B v w = 0) → w = 0) →
    Even (Module.finrank 𝕜 V) ∧
      (Nontrivial V → 2 ≤ Module.finrank 𝕜 V)

/-- The standard symplectic plane has isotropic lines, and symplectic
monodromy need not preserve a coefficient line. -/
def symplecticCoefficientLinesNeedNotBeInvariant : Prop :=
  let V := Fin 2 → ℝ
  let ω : V → V → ℝ := fun v w => v 0 * w 1 - v 1 * w 0
  let e₁ : V := ![1, 0]
  let L₁ : Submodule ℝ V := Submodule.span ℝ ({e₁} : Set V)
  let isotropic : Submodule ℝ V → Prop := fun L =>
    ∀ v ∈ L, ∀ w ∈ L, ω v w = 0
  let symplectic : (V ≃ₗ[ℝ] V) → Prop := fun A =>
    ∀ v w, ω (A v) (A w) = ω v w
  let preserves : (V ≃ₗ[ℝ] V) → Submodule ℝ V → Prop := fun A L =>
    ∀ v ∈ L, A v ∈ L
  (∀ v ∈ L₁, ∀ w ∈ L₁, ω v w = 0) ∧
    (∀ L : Submodule ℝ V, Module.finrank ℝ L = 1 → isotropic L) ∧
    (∃ A : V ≃ₗ[ℝ] V,
      symplectic A ∧
        ¬(∃ L : Submodule ℝ V,
          Module.finrank ℝ L = 1 ∧ preserves A L))

/-- The determinant of one minus a matrix times the indeterminate. -/
noncomputable def localEulerDenominator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  Matrix.det
    ((1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) -
      (Polynomial.X : Polynomial ℂ) •
        (Matrix.map A (algebraMap ℂ (Polynomial ℂ)) :
          Matrix (Fin n) (Fin n) (Polynomial ℂ)))

/-- A positive-dimensional symplectic local representation has an even rank at
least two, and its local determinant cannot be the rank-one factor. -/
def symplecticLocalEulerDenominatorIsNotRankOne : Prop :=
  ∀ (n : ℕ) (J A : Matrix (Fin n) (Fin n) ℂ),
    0 < n →
    (J.transpose = -J) →
    (Matrix.det J ≠ 0) →
    (A.transpose * J * A = J) →
    Even n ∧ 2 ≤ n ∧
      localEulerDenominator A ≠ 1 - Polynomial.X

end MathlibPlus.Open.LinearAlgebra
