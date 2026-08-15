import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The complex half-plane parameter used by the normalized half-line kernels. -/
def halfPlaneParameter (y t : ℝ) : ℂ := (y : ℂ) - Complex.I * t

/-- The normalized Laplace kernel as a pointwise complex-valued function. -/
def halfLineLaplaceKernel (y t : ℝ) (x : ℝ) : ℂ :=
  (Real.sqrt (2 * y) : ℂ) * Complex.exp (-halfPlaneParameter y t * x)

/-- Claim 3299: normalized half-line Laplace kernels and their Gram entries. -/
def claim3299 (n : ℕ) (y t : Fin n → ℝ)
    (hy : ∀ j, 0 < y j) : Prop :=
  (∀ j, MemLp (halfLineLaplaceKernel (y j) (t j)) 2
      (volume.restrict (Ioi (0 : ℝ))) ∧
    eLpNorm (halfLineLaplaceKernel (y j) (t j)) 2
      (volume.restrict (Ioi (0 : ℝ))) = 1) ∧
    ∀ j k,
      ∫ x : ℝ,
        star (halfLineLaplaceKernel (y k) (t k) x) *
          halfLineLaplaceKernel (y j) (t j) x
          ∂(volume.restrict (Ioi (0 : ℝ))) =
        ((2 : ℂ) * Real.sqrt (y j * y k)) /
          (halfPlaneParameter (y j) (t j) +
            star (halfPlaneParameter (y k) (t k)))

/-- The finite separation product appearing in Claim 3300. -/
def separationProduct {n : ℕ} (s : Fin n → ℂ) (j : Fin n) : ℝ :=
  (Finset.univ.erase j).prod (fun k =>
    ‖(s j - s k) / (s j + star (s k))‖)

/-- Claim 3300: the finite half-plane separation products and their minimum. -/
def claim3300 (n : ℕ) (y t : Fin n → ℝ)
    (hy : ∀ j, 0 < y j) : Prop :=
  let s : Fin n → ℂ := fun j => halfPlaneParameter (y j) (t j)
  ∃ δ : Fin n → ℝ, ∃ δstar : ℝ,
    (∀ j, δ j = separationProduct s j) ∧
      (∀ j, δstar ≤ δ j) ∧ (∃ j, δstar = δ j)

/-- Claim 3304: the gap-and-strip pairwise lower bound. -/
def claim3304 (n : ℕ) (y t : Fin (n + 1) → ℝ)
    (Y d L : ℝ)
    (hy : ∀ j, 0 < y j ∧ y j ≤ Y)
    (hgap : ∀ j : Fin n,
      t (Fin.succ j) - t (Fin.castSucc j) ≥ d / L) : Prop :=
  ∀ j k : Fin (n + 1), j ≠ k →
    ‖(halfPlaneParameter (y j) (t j) -
        halfPlaneParameter (y k) (t k)) /
      (halfPlaneParameter (y j) (t j) +
        star (halfPlaneParameter (y k) (t k)))‖ ≥
      (d * |((j : ℤ) - (k : ℤ))| / L) /
        Real.sqrt ((d * |((j : ℤ) - (k : ℤ))| / L) ^ 2 + 4 * Y ^ 2)
end MathlibPlus.Open.ResearchFormalization.Batch
