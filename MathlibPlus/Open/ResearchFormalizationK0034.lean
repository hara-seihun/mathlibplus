import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationK0034

/-- The rising factorial `(x)_n`, written as a finite product. -/
def risingFactorial (x : ℂ) (n : ℕ) : ℂ :=
  Finset.prod (Finset.range n) (fun r => x + (r : ℂ))

/-- The alternating one-sided Schur pivots from the admitted formula. -/
noncomputable def schurPivot (α : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * ((4 : ℂ)⁻¹) ^ j * (j.factorial : ℂ) * risingFactorial α j

noncomputable def complexTwoPower (w : ℂ) : ℂ := Complex.cpow (2 : ℂ) w

noncomputable def pssScalar (s α : ℂ) : ℂ := complexTwoPower (2 - s) / α

noncomputable def pssTowerTerm (s : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j *
    complexTwoPower (2 - s - 2 * (j : ℂ)) *
    (j.factorial : ℂ)

/-- Claim 7799: the PSS scalar has a pure dyadic first pivot, while all
higher pivots retain their nonconstant rising-factorial factor. -/
def minimalPssScalarFlattensOnlyFirstPivot : Prop :=
  (∀ (s k : ℂ) (j : ℕ),
      1 ≤ j →
      s + k - 1 ≠ 0 →
      pssScalar s (s + k - 1) * schurPivot (s + k - 1) j =
        pssTowerTerm s j * risingFactorial (s + k - 1 + 1) (j - 1)) ∧
  (∀ (s k : ℂ),
      s + k - 1 ≠ 0 →
      pssScalar s (s + k - 1) * schurPivot (s + k - 1) 1 =
        -complexTwoPower (-s)) ∧
  (∀ (j : ℕ),
      2 ≤ j →
      ¬(∀ x y : ℂ,
          risingFactorial (x + 1) (j - 1) =
            risingFactorial (y + 1) (j - 1))) ∧
  (∀ (s α : ℂ),
      α ≠ 0 →
      ∀ q : ℂ, ∃ j : ℕ,
        1 ≤ j ∧ q * schurPivot α j ≠ pssTowerTerm s j)

noncomputable def criticalS (τ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (τ : ℂ)

noncomputable def alphaPlus (k : ℝ) (τ : ℝ) : ℂ :=
  criticalS τ + (k : ℂ) - 1

noncomputable def alphaMinus (k : ℝ) (τ : ℝ) : ℂ :=
  (k : ℂ) - criticalS τ

noncomputable def realShape (k : ℝ) : ℂ :=
  (k : ℂ) - (1 / 2 : ℂ)

noncomputable def gammaPlus (k : ℝ) (τ : ℝ) : ℂ :=
  Complex.Gamma (alphaPlus k τ) / Complex.Gamma (realShape k)

noncomputable def gammaMinus (k : ℝ) (τ : ℝ) : ℂ :=
  Complex.Gamma (alphaMinus k τ) / Complex.Gamma (realShape k)

noncomputable def sechKernel (z : ℂ) : ℂ :=
  (Complex.cosh (z / 2))⁻¹

noncomputable def lowerOffDiagonalOverlap (k : ℝ) (τ : ℝ) (z : ℂ) : ℂ :=
  gammaPlus k τ * (Complex.cpow (sechKernel z) (alphaPlus k τ))

noncomputable def reflectedLowerOffDiagonalOverlap
    (k : ℝ) (τ : ℝ) (z : ℂ) : ℂ :=
  gammaMinus k τ * (Complex.cpow (sechKernel z) (alphaMinus k τ))

/-- Claim 7815: the lower off-diagonal kernel has the first PSS-normalized
chiral Schur line, and reflection gives the conjugate line. -/
def offDiagonalKernelDerivativeIsFirstPSSPivot : Prop :=
  ∀ (k : ℝ) (τ : ℝ),
    0 < k - 1 / 2 →
    iteratedDeriv 2 (lowerOffDiagonalOverlap k τ) 0 =
        -(alphaPlus k τ / 4) * gammaPlus k τ ∧
    (complexTwoPower (2 - criticalS τ) / alphaPlus k τ) *
        iteratedDeriv 2 (lowerOffDiagonalOverlap k τ) 0 =
      -complexTwoPower (-criticalS τ) * gammaPlus k τ ∧
    iteratedDeriv 2 (reflectedLowerOffDiagonalOverlap k τ) 0 =
        -(alphaMinus k τ / 4) * gammaMinus k τ ∧
    (complexTwoPower (2 - (1 - criticalS τ)) / alphaMinus k τ) *
        iteratedDeriv 2 (reflectedLowerOffDiagonalOverlap k τ) 0 =
      -complexTwoPower (-(1 - criticalS τ)) * gammaMinus k τ

end MathlibPlus.Open.ResearchFormalizationK0034
