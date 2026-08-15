import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization

/-- The explicit Gram-matrix meaning of positive definiteness for a complex-valued
function on the additive real line. -/
def complexPositiveDefinite (a : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    let gramSum : ℂ :=
      ∑ i, ∑ j, star (c i) * a (x i - x j) * c j
    0 ≤ gramSum.re ∧ gramSum.im = 0

/-- Reciprocal positive-definite functions are characters, with the real-even
case reduced to the constant character. -/
def claim3172 : Prop :=
  ∀ a : ℝ → ℂ,
    Continuous a → complexPositiveDefinite a → a 0 = 1 →
      (∀ x : ℝ, a x ≠ 0) →
      complexPositiveDefinite (fun x => (a x)⁻¹) →
      (∃ lam : ℝ, ∀ x : ℝ,
        a x = Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) ∧
        ((∀ x : ℝ, (a x).im = 0 ∧ a (-x) = a x) →
          ∀ x : ℝ, a x = 1)

/-- Equality in the unit-modulus case forces the character law. -/
def claim3173 : Prop :=
  ∀ a : ℝ → ℂ,
    complexPositiveDefinite a → a 0 = 1 →
      (∀ x : ℝ, ‖a x‖ = 1) →
      ∀ x z : ℝ, a (x + z) = a x * a z

/-- Autocorrelation of a nonzero even square-integrable real profile. -/
def claim3174 : Prop :=
  ∀ w : ℝ → ℝ,
    MeasureTheory.Integrable (fun x => ‖w x‖ ^ 2) (MeasureTheory.MeasureSpace.volume) →
      (∀ x : ℝ, w (-x) = w x) →
      (¬∀ᵐ x : ℝ ∂MeasureTheory.MeasureSpace.volume, w x = 0) →
      let A : ℝ → ℝ := fun D => ∫ x, w x * w (x + D)
      (complexPositiveDefinite (fun D => (A D : ℂ)) ∧
        0 < A 0 ∧
        Filter.Tendsto A (Filter.cocompact ℝ) (𝓝 0)) ∧
      ((∀ᵐ x : ℝ ∂MeasureTheory.MeasureSpace.volume, 0 < w x) → ∀ D : ℝ, 0 < A D)

end MathlibPlus.Open.ResearchFormalization
