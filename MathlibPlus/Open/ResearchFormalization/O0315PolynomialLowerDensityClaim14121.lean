import Mathlib

open MeasureTheory
open Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0315PolynomialLowerDensityClaim14121

noncomputable section

/-- The zero-bearing disk and retained boundary data from the slit setup. -/
private def zeroBearingSlitContext
    (c : ℂ) (r T₀ ε : ℝ) (m : ℕ) : Prop :=
  0 < r ∧
    0 < T₀ ∧
    0 < m ∧
    let D := Metric.closedBall c r
    let Γ := Metric.sphere c r
    IsCompact D ∧
      IsSimplyConnected D ∧
      D ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re ∧ s.re < 1} ∧
      (∀ s ∈ Γ, riemannZeta s ≠ 0) ∧
      (∃ Z : Multiset ℂ,
        Z.card = m ∧
          (∀ z, z ∈ Z → z ∈ Metric.ball c r ∧ riemannZeta z = 0) ∧
          (∀ z : ℂ, z ∈ Metric.ball c r → riemannZeta z = 0 →
            ∀ k : ℕ,
              Multiset.count z Z = k ↔
                ((∀ j < k, iteratedDeriv j riemannZeta z = 0) ∧
                  iteratedDeriv k riemannZeta z ≠ 0))) ∧
      0 < ε ∧
      ε < (1 / 4 : ℝ) *
        sInf {v : ℝ | ∃ s ∈ Γ, v = ‖riemannZeta s‖}

/-- A smoothly parameterized retained boundary is exactly the boundary with
its open arc removed, with the arc length used as the parameter. -/
private def retainedBoundaryFamily
    (c : ℂ) (r ell₀ : ℝ) (K : ℝ → Set ℂ) : Prop :=
  0 < ell₀ ∧
    ∀ ell : ℝ, 0 < ell → ell < ell₀ →
      ∃ (J I : Set ℂ) (a b : ℂ) (gamma : ℝ → ℂ),
        ContDiffOn ℝ 1 gamma (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            gamma t ∈ Metric.sphere c r) ∧
          J = gamma '' Set.Ioo (0 : ℝ) 1 ∧
          I = closure J ∧
          K ell = Metric.sphere c r \ J ∧
          a = gamma 0 ∧
          b = gamma 1 ∧
          ell = ∫ t in (0 : ℝ)..1, ‖deriv gamma t‖

/-- The exact recurrence event on the retained boundary `K_ell`. -/
private def slitRecurrenceEvent
    (K : ℝ → Set ℂ) (ε ell T : ℝ) : Set ℝ :=
  {τ : ℝ |
    T ≤ τ ∧
      τ ≤ 2 * T ∧
        sSup
            {v : ℝ |
              ∃ s ∈ K ell,
                v =
                  ‖riemannZeta (s + (τ : ℂ) * Complex.I) -
                    riemannZeta s‖} < ε}

/-- The literal vertical-shift upper density of the same slit event. -/
private noncomputable def slitRecurrenceDensity
    (K : ℝ → Set ℂ) (ε ell : ℝ) : ℝ :=
  Filter.limsup
    (fun T : ℝ =>
      (MeasureTheory.volume (slitRecurrenceEvent K ε ell T)).toReal / T)
    Filter.atTop

/-- The inverse-square tail delivered by generic independent Euler support,
with the event and its density fixed to the zero-bearing slit above. -/
private def genericIndependentEulerSupport
    (K : ℝ → Set ℂ) (ε ell₀ C κ : ℝ) : Prop :=
  0 < C ∧
    0 < κ ∧
      ∀ ell : ℝ, 0 < ell → ell < ell₀ →
        slitRecurrenceDensity K ε ell ≤
          C * Real.exp (-κ / ell ^ 2)

/-- A polynomial lower density for that very same recurrence event. -/
private def polynomialLowerDensity
    (K : ℝ → Set ℂ) (ε ell₀ : ℝ) : Prop :=
  ∃ (A c ell₁ : ℝ),
    0 < A ∧
      0 < c ∧
        0 < ell₁ ∧
          ∀ ell : ℝ, 0 < ell → ell < min ell₀ ell₁ →
            c * Real.rpow ell A ≤ slitRecurrenceDensity K ε ell

/-- The inverse-square exponential is little-o of every fixed positive power
at the shrinking positive slit. -/
private def inverseSquareIsLittleO (κ A : ℝ) : Prop :=
  Tendsto
    (fun ell : ℝ =>
      Real.exp (-κ / ell ^ 2) / Real.rpow ell A)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (𝓝 0)

/-- Generic independent Euler support, including any zero-free-logarithm,
finite-prime phase, or Cameron--Martin argument that yields its inverse-square
upper tail, cannot supply a polynomial lower density for the same
zero-bearing slit event. -/
def polynomialLowerDensityCannotComeFromGenericEulerSupport_claim14121 : Prop :=
  ∀ (c : ℂ) (r T₀ ε : ℝ) (m : ℕ)
    (ell₀ : ℝ) (K : ℝ → Set ℂ),
    zeroBearingSlitContext c r T₀ ε m →
      retainedBoundaryFamily c r ell₀ K →
        (∀ κ A : ℝ, 0 < κ → 0 < A →
          inverseSquareIsLittleO κ A) ∧
          (∀ C κ : ℝ,
            genericIndependentEulerSupport K ε ell₀ C κ →
              ¬ polynomialLowerDensity K ε ell₀)

end

end MathlibPlus.Open.ResearchFormalization.O0315PolynomialLowerDensityClaim14121
