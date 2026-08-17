import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0043Claim17444

noncomputable section

/-- The degree-`N` Taylor section at the origin of the entire function `F`. -/
def taylorSection (F : ℂ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z =>
    ∑ n ∈ Finset.range (N + 1),
      (iteratedDeriv n F 0 / (Nat.factorial n : ℂ)) * z ^ n

/-- The open disk of radius `R`. -/
def openDisk (R : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < R}

/-- The zero carrier used by the multiplicity count. -/
def diskZeroSet (F : ℂ → ℂ) (R : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ openDisk R ∧ F z = 0}

/-- Zeros in the open disk, counted with their analytic orders. -/
def diskZeroCount (F : ℂ → ℂ) (R : ℝ) : ℕ :=
  ∑' z : {z : ℂ // z ∈ diskZeroSet F R},
    analyticOrderNatAt F z.1

/-- `m_R` is the positive minimum of `|F|` on the circle `|z|=R`. -/
def positiveBoundaryMinimum
    (F : ℂ → ℂ) (R m_R : ℝ) : Prop :=
  0 < m_R ∧
    ∃ z₀ : ℂ,
      ‖z₀‖ = R ∧ ‖F z₀‖ = m_R ∧
        ∀ z : ℂ, ‖z‖ = R → m_R ≤ ‖F z‖

/-- The exact exponential-type Taylor-section error scale. -/
def taylorRemainder (A τ R : ℝ) (N : ℕ) : ℝ :=
  2 * A * Real.exp (2 * τ * R) *
    Real.rpow (2 : ℝ) (-((N : ℝ) + 1))

/-- Claim 17444: under the exponential-type Taylor setup and a positive
contour margin, the strict Rouché inequality transfers the open-disk zero
count, with analytic multiplicities, from `F` to its degree-`N` Taylor
section. -/
def claim17444 : Prop :=
  ∀ (F : ℂ → ℂ) (A τ R m_R : ℝ) (N : ℕ),
    Differentiable ℂ F →
    (∀ z : ℂ, ‖F z‖ ≤ A * Real.exp (τ * ‖z‖)) →
    0 ≤ R →
    positiveBoundaryMinimum F R m_R →
    taylorRemainder A τ R N < m_R →
    diskZeroCount F R = diskZeroCount (taylorSection F N) R

end

end MathlibPlus.Open.ResearchFormalization.R0043Claim17444
