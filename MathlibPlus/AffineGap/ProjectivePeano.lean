import Mathlib

/-!
# Projective Peano data

Definitions needed to state the all-rank projective Peano identity from source record
packet `C-0005`.
-/

namespace MathlibPlus.AffineGap.ProjectivePeano

/-- The affine sample determinant with rows `(1, γ(qᵢ))`. The curve has `n`
coordinates, so the affine determinant has rank `n + 1`. -/
noncomputable def affineSampleDet {n : ℕ} (γ : ℝ → Fin n → ℝ)
    (q : Fin (n + 1) → ℝ) : ℝ :=
  Matrix.det fun i j => Fin.cases (1 : ℝ) (fun k => γ (q i) k) j

/-- The determinant whose rows are coordinatewise tangent vectors sampled at `s`. -/
noncomputable def tangentVolume {n : ℕ} (γ : ℝ → Fin n → ℝ)
    (s : Fin n → ℝ) : ℝ :=
  Matrix.det fun i j => deriv (fun t => γ t j) (s i)

/-- The Cartesian product of the `n` consecutive closed knot gaps. -/
def consecutiveGapBox {n : ℕ} (q : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  {s | ∀ i, s i ∈ Set.Icc (q i.castSucc) (q i.succ)}

/-- Product-Lebesgue form of the iterated integral which draws exactly one tangent
from each consecutive gap. Under a `C¹` hypothesis this is the displayed iterated
interval integral by Fubini. -/
noncomputable def consecutiveGapTangentIntegral {n : ℕ} (γ : ℝ → Fin n → ℝ)
    (q : Fin (n + 1) → ℝ) : ℝ :=
  ∫ s in consecutiveGapBox q, tangentVolume γ s

end MathlibPlus.AffineGap.ProjectivePeano
