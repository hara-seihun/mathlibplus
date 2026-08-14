import Mathlib

noncomputable section
open MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization

/-- The odd extension and weighted constant used by the Poisson-edge packet. -/
def nonzeroOddBumpPoissonEdgeConstant : Prop :=
  ∀ (betaPlus : ℝ → ℝ),
    ContDiff ℝ ⊤ betaPlus →
    (∀ x : ℝ, 0 ≤ betaPlus x) →
    Function.support betaPlus ⊆ Ioo (1 : ℝ) 2 →
    (∃ x : ℝ, betaPlus x ≠ 0) →
    ∃ beta : ℝ → ℝ,
      (∀ x : ℝ, 0 ≤ x → beta x = betaPlus x) ∧
      (∀ x : ℝ, beta (-x) = -beta x) ∧
      let Cbeta : ℝ := -(1 / (2 * Real.pi)) *
        ∫ x in Ioi (0 : ℝ), beta x / x
      Cbeta ≠ 0

private def ghostLambda (L : ℝ) : ℝ := Real.exp L

private def ghostAmplitude (Cβ c : ℝ) (m : ℕ) (σ₀ L : ℝ) : ℝ :=
  -(2 * c / Cβ) * (L⁻¹) ^ m * Real.rpow (ghostLambda L) (1 - σ₀)

private def ghostRZero (β : ℝ → ℝ) (Cβ c : ℝ) (m : ℕ) (σ₀ L : ℝ)
    (x : ℝ) : ℝ :=
  ghostAmplitude Cβ c m σ₀ L * β (x / L) *
    Real.sin (2 * Real.pi * ghostLambda L * x)

private def ghostEpsilon (β : ℝ → ℝ) (Cβ c : ℝ) (m : ℕ) (σ₀ L : ℝ) : ℝ :=
  ∫ x : ℝ, ghostRZero β Cβ c m σ₀ L x

private def ghostPL (p : ℝ → ℝ) (L x : ℝ) : ℝ :=
  L⁻¹ * p (x / L)

private def ghostR (β p : ℝ → ℝ) (Cβ c : ℝ) (m : ℕ) (σ₀ L : ℝ) (x : ℝ) : ℝ :=
  ghostRZero β Cβ c m σ₀ L x -
    ghostEpsilon β Cβ c m σ₀ L * ghostPL p L x

/-- The exact definitions of the arithmetic ghost packet. -/
def exactS0ArithmeticGhostPacketConstruction : Prop :=
  ∀ (σ₀ c Cβ L : ℝ) (m : ℕ) (β p : ℝ → ℝ),
    1 < σ₀ → Cβ ≠ 0 → 0 < L →
    Cβ = -(1 / (2 * Real.pi)) * ∫ x in Ioi (0 : ℝ), β x / x →
    ContDiff ℝ ⊤ p →
    (∀ x : ℝ, p (-x) = p x) →
    Function.support p ⊆ Icc (-2 : ℝ) (-1) ∪ Icc 1 2 →
    (∫ x : ℝ, p x) = 1 →
    ∃ r₀ : ℝ → ℝ, ∃ ε : ℝ, ∃ pL r : ℝ → ℝ,
      (∀ x : ℝ,
        r₀ x = ghostAmplitude Cβ c m σ₀ L * β (x / L) *
          Real.sin (2 * Real.pi * ghostLambda L * x)) ∧
      ε = ∫ x : ℝ, r₀ x ∧
      (∀ x : ℝ, pL x = L⁻¹ * p (x / L)) ∧
      (∀ x : ℝ, r x = r₀ x - ε * pL x)

/-- Symmetry, exact constraints, support, and endpoint traces of the packet. -/
def packetSymmetryExactConstraintsAndSupport : Prop :=
  ∀ (σ₀ c Cβ : ℝ) (m : ℕ) (β p : ℝ → ℝ),
    1 < σ₀ → Cβ ≠ 0 →
    Cβ = -(1 / (2 * Real.pi)) * ∫ x in Ioi (0 : ℝ), β x / x →
    ContDiff ℝ ⊤ β →
    (∀ x : ℝ, β (-x) = -β x) →
    Function.support β ⊆ Ioo (-2 : ℝ) (-1) ∪ Ioo 1 2 →
    ContDiff ℝ ⊤ p →
    (∀ x : ℝ, p (-x) = p x) →
    Function.support p ⊆ Icc (-2 : ℝ) (-1) ∪ Icc 1 2 →
    (∫ x : ℝ, p x) = 1 →
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        let r : ℝ → ℝ := ghostR β p Cβ c m σ₀ L
        ContDiff ℝ ⊤ r ∧
          (∀ x : ℝ, r (-x) = r x) ∧
          Function.support r ⊆ Icc (-2 * L) (-L) ∪ Icc L (2 * L) ∧
          r 0 = 0 ∧
          (∫ x : ℝ, r x) = 0 ∧
          (∀ k : ℕ,
            iteratedDeriv k r (-2 * L) = 0 ∧
            iteratedDeriv k r (-L) = 0 ∧
            iteratedDeriv k r L = 0 ∧
            iteratedDeriv k r (2 * L) = 0)

end MathlibPlus.Open.ResearchFormalization
