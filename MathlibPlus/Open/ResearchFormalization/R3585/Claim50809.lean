import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R3585.Claim50809

abbrev PositiveIndex := {k : ℕ // 1 ≤ k}

/-- The explicit reflected Euler atom with p = 2 and r = 2. -/
def reflectedAtom (z : ℂ) : ℂ :=
  (1 + (2 : ℂ) * Complex.exp ((Real.log 2 : ℂ) * z)) *
    (1 + (2 : ℂ) * Complex.exp (-((Real.log 2 : ℂ) * z)))

/-- The literal coefficient of a positive-amplitude reflected atom. -/
def literalEulerCoefficient (p : ℕ) (r : ℝ) (k : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * (-1 : ℂ) ^ k *
    (Real.rpow (p : ℝ) ((k : ℝ) / 2) : ℂ) *
      ((r ^ k + (r ^ k)⁻¹ - 2 : ℝ) : ℂ)

/-- Finite exponential type is the temperedness carrier for this explicit
finite reflected factor. -/
def tempered : Prop :=
  ∃ C τ : ℝ, 0 ≤ C ∧ 0 ≤ τ ∧
    ∀ z : ℂ, ‖reflectedAtom z‖ ≤ C * Real.exp (τ * ‖z‖)

/-- The two reflected vertical lines contain zeros of the explicit factor. -/
def reflectedLineZeros : Prop :=
  (∃ z : ℂ, reflectedAtom z = 0 ∧ z.re = 1) ∧
    ∃ z : ℂ, reflectedAtom z = 0 ∧ z.re = -1

/-- Preservation of the literal prime-power tower by this one factor. -/
def preservesLiteralEulerTower : Prop :=
  ∀ k : PositiveIndex, literalEulerCoefficient 2 2 k.1 = 0

/-- The displayed first literal coefficient of the explicit factor. -/
def explicitLiteralCoefficient : ℂ :=
  literalEulerCoefficient 2 2 1

/-- The explicit off-critical factor is even and tempered, has zeros on both
reflected lines, and cannot be a nonzero mode preserving the literal tower. -/
def claim50809 : Prop :=
  (∀ z : ℂ, reflectedAtom (-z) = reflectedAtom z) ∧
    tempered ∧
    reflectedLineZeros ∧
    explicitLiteralCoefficient =
      -(Real.log 2 : ℂ) *
        (Real.rpow 2 (1 / 2 : ℝ) : ℂ) *
          ((2 : ℂ) + (1 / 2 : ℂ) - 2) ∧
    explicitLiteralCoefficient ≠ 0 ∧
    ¬ ((∃ z : ℂ, reflectedAtom z ≠ 0) ∧
      preservesLiteralEulerTower)

end MathlibPlus.Open.ResearchFormalization.R3585.Claim50809

end
