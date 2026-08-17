import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0205

private noncomputable def counterfeitMultiplier
    (F : ℂ → ℂ) (L q : ℝ) (z : ℂ) : ℂ :=
  F z * (1 + (q : ℂ) * Complex.cosh ((L : ℂ) * z))

/-- A finite test factors through a finite-dimensional data space, with both
its data map and its test on that data continuous.  The data map is left
arbitrary: it is not identified with a Taylor jet. -/
private def dependsOnFiniteContinuousData (T : (ℂ → ℂ) → ℝ) : Prop :=
  ∃ k : ℕ,
    ∃ data : (ℂ → ℂ) → (Fin k → ℂ),
      ∃ τ : (Fin k → ℂ) → ℝ,
        Continuous data ∧ Continuous τ ∧
          ∀ F : ℂ → ℂ, T F = τ (data F)

private def nestedFiniteContinuousHierarchy
    (T : ℕ → (ℂ → ℂ) → ℝ) : Prop :=
  (∀ d : ℕ, dependsOnFiniteContinuousData (T d)) ∧
    ∀ d : ℕ, ∀ F : ℂ → ℂ,
      0 < T (d + 1) F → 0 < T d F

private def uncancelledOffAxisMultiplierZeros
    (F : ℂ → ℂ) (L : ℝ) : Prop :=
  ∃ q₀ : ℝ, 0 < q₀ ∧
    ∀ q : ℝ, 0 < q → q < q₀ →
      ∃ z : ℂ,
        z.re ≠ 0 ∧ F z ≠ 0 ∧
          1 + (q : ℂ) * Complex.cosh ((L : ℂ) * z) = 0

/-- No finite depth of a nested hierarchy of strict continuous finite-data
tests certifies global axis purity against the multiplicative cosh
counterfeit.  The noncancellation premise is quantified only on a sufficiently
small positive-q interval, as in the perturbation statement. -/
def boundedFiniteSectionsCannotControlGlobalAxisPurity_claim18803 : Prop :=
  ∀ (D : ℕ) (T : ℕ → (ℂ → ℂ) → ℝ)
    (F : ℂ → ℂ) (L : ℝ),
    nestedFiniteContinuousHierarchy T →
      (∀ d : ℕ, 0 < T (d + 1) F) →
      Differentiable ℂ F →
      L ≠ 0 →
      uncancelledOffAxisMultiplierZeros F L →
      ∃ q_D : ℝ, 0 < q_D ∧
        ∀ q : ℝ, 0 < q → q < q_D →
          (∀ d : Fin D,
            0 < T (d.1 + 1)
              (fun z : ℂ => counterfeitMultiplier F L q z)) ∧
          ∃ z : ℂ,
            z.re ≠ 0 ∧ counterfeitMultiplier F L q z = 0

end MathlibPlus.Open.NewResearch2.R0205
