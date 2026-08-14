import Mathlib

namespace MathlibPlus.Open.K0069

noncomputable section

/-- The scalar autocorrelation kernel from the admitted statement. -/
def autocorrelation (w : ℝ → ℝ) (D : ℝ) : ℝ :=
  ∫ v : ℝ, w (v - D) * w (v + D)

/-- The scalar first-Laguerre kernel from the admitted statement. -/
def firstLaguerre (w : ℝ → ℝ) (D : ℝ) : ℝ :=
  ∫ v : ℝ, v ^ 2 * w (v - D) * w (v + D)

/-- The exact cross-Gram matrix displayed in the admitted statement. -/
def tensorCrossGram (n : ℕ) (w : ℝ → ℝ) (D : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ autocorrelation w D ^ n,
      (n : ℝ) * D * autocorrelation w D ^ n;
      -(n : ℝ) * D * autocorrelation w D ^ n,
      (n : ℝ) * autocorrelation w D ^ (n - 1) * firstLaguerre w D
        - (n : ℝ) ^ 2 * D ^ 2 * autocorrelation w D ^ n ]

/-- Positive definiteness for a real `2 × 2` matrix-valued kernel on `ℝ`. -/
def MatrixValuedPositiveDefiniteKernel
    (K : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → ℝ) (c : Fin m → Fin 2 → ℝ),
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, ∑ a : Fin 2, ∑ b : Fin 2,
      c i a * K (x i - x j) a b * c j b

/--
For every positive integer `n`, the displayed matrix-valued kernel is
positive definite, for every real even source satisfying the stated `L²`
conditions.
-/
def matrixValuedPositiveDefiniteness (w : ℝ → ℝ) : Prop :=
  (∀ u : ℝ, w (-u) = w u) →
  MeasureTheory.MemLp w 2 MeasureTheory.volume →
  MeasureTheory.MemLp (fun u : ℝ => u * w u) 2 MeasureTheory.volume →
  ∀ (n : ℕ), 0 < n →
    MatrixValuedPositiveDefiniteKernel (fun D : ℝ => tensorCrossGram n w D)

end
end MathlibPlus.Open.K0069
