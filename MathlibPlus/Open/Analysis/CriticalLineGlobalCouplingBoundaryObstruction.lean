import Mathlib

open Matrix

namespace MathlibPlus.Open.Analysis.CriticalLineGlobalCouplingBoundaryObstruction

/-- The companion block from the admitted local obstruction. -/
def companion (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, -2 * c]

/-- The local invariant-block condition-number obstruction. -/
def coupling_lower_bound : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticForm ℝ V) (T : V →ₗ[ℝ] V) (c m M : ℝ),
    (∀ v, m * ‖v‖ ^ 2 ≤ Q v ∧ Q v ≤ M * ‖v‖ ^ 2) →
    (∀ v, Q (T v) = Q v) →
    0 < m →
    0 ≤ c →
    c < 1 →
    (∃ e : (Fin 2 → ℝ) →ₗ[ℝ] V,
      (∀ x, inner ℝ (e x) (e x) = x ⬝ᵥ x) ∧
      (∀ x, T (e x) = e (companion c *ᵥ x))) →
    m * (1 + c) ≤ M * (1 - c) ∧
    M / m ≥ (1 + c) / (1 - c)

/-- The boundary family forces the stated linear lower bound on distortion. -/
def boundary_stage_distortion : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticForm ℝ V) (T : V →ₗ[ℝ] V) (m M : ℝ) (n : ℕ),
    (∀ v, m * ‖v‖ ^ 2 ≤ Q v ∧ Q v ≤ M * ‖v‖ ^ 2) →
    (∀ v, Q (T v) = Q v) →
    0 < m →
    (∃ e : (Fin 2 → ℝ) →ₗ[ℝ] V,
      (∀ x, inner ℝ (e x) (e x) = x ⬝ᵥ x) ∧
      (∀ x,
        T (e x) =
          e (companion (1 - 1 / (n + 2 : ℝ)) *ᵥ x))) →
    (2 * n + 3 : ℝ) * m ≤ M ∧
    M / m ≥ (2 * n + 3 : ℝ)

/-- No bounded and coercive invariant quadratic form can contain every
boundary block, regardless of its off-diagonal couplings. -/
def no_single_bounded_coercive_boundary_gluing : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticForm ℝ V) (T : V →ₗ[ℝ] V),
    ¬ ∃ (m M : ℝ),
      0 < m ∧
      (∀ v,
        m * ‖v‖ ^ 2 ≤ Q v ∧ Q v ≤ M * ‖v‖ ^ 2) ∧
      (∀ v, Q (T v) = Q v) ∧
      (∀ n : ℕ,
        ∃ e : (Fin 2 → ℝ) →ₗ[ℝ] V,
          (∀ x, inner ℝ (e x) (e x) = x ⬝ᵥ x) ∧
          (∀ x,
            T (e x) =
              e (companion (1 - 1 / (n + 2 : ℝ)) *ᵥ x)))

end MathlibPlus.Open.Analysis.CriticalLineGlobalCouplingBoundaryObstruction
