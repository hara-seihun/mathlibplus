import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MathlibPlus.Open.Analysis

/-- Claim 10627: strict total positivity of the shifted rising-factorial rows,
together with the column-scaled form in which column `q` is divided by `(2q)!`.
The rising factorial is Mathlib's `ascPochhammer` evaluated at `α`; row and
column indices are represented by strictly monotone maps from `Fin k`. -/
def strictTotalPositivityShiftedGammaRows_10627 : Prop :=
  ∀ (α : ℝ), 0 < α →
    ∀ (k : ℕ) (p q : Fin k → ℕ), StrictMono p → StrictMono q →
      0 < Matrix.det (fun i j ↦
        (ascPochhammer ℝ (p i + q j)).eval α) ∧
      0 < Matrix.det (fun i j ↦
        (ascPochhammer ℝ (p i + q j)).eval α /
          (Nat.factorial (2 * q j) : ℝ))

end MathlibPlus.Open.Analysis
