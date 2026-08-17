import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0205

private noncomputable def finiteDataCounterfeitMultiplier
    (F : ℂ → ℂ) (L q : ℝ) (z : ℂ) : ℂ :=
  F z * (1 + (q : ℂ) * Complex.cosh ((L : ℂ) * z))

private def finiteDataTest18799 (T : (ℂ → ℂ) → ℝ) : Prop :=
  ∃ k : ℕ,
    ∃ data : (ℂ → ℂ) → (Fin k → ℂ),
      ∃ test : (Fin k → ℂ) → ℝ,
        Continuous data ∧ Continuous test ∧
          ∀ F : ℂ → ℂ, T F = test (data F)

private def nestedFiniteDataHierarchy18799
    (T : ℕ → (ℂ → ℂ) → ℝ) : Prop :=
  (∀ d : ℕ, finiteDataTest18799 (T d)) ∧
    ∀ d : ℕ, ∀ F : ℂ → ℂ,
      0 < T (d + 1) F → 0 < T d F

/-- Finite strict continuous levels remain strict for the exact
multiplicative cosh perturbation, uniformly over every fixed finite depth. -/
def claim18799_finiteStrictContinuousTestsUnderCounterfeit : Prop :=
  ∀ (D : ℕ) (T : ℕ → (ℂ → ℂ) → ℝ)
    (F : ℂ → ℂ) (L : ℝ),
    nestedFiniteDataHierarchy18799 T →
      (∀ d : ℕ, 0 < T (d + 1) F) →
      Differentiable ℂ F →
      ∃ q_D : ℝ, 0 < q_D ∧
        ∀ q : ℝ, 0 < q → q < q_D →
          ∀ d : Fin D,
            0 < T (d.1 + 1)
              (fun z : ℂ => finiteDataCounterfeitMultiplier F L q z)

end MathlibPlus.Open.NewResearch2.R0205
