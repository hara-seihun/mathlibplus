import Mathlib
import MathlibPlus.Open.Analysis.HarmonicCharacterSeries

namespace MathlibPlus.Open.Analysis.Claim7092

open MathlibPlus.Open

abbrev WeightGrid (k : ℕ) := Fin (k + 1) × Fin (k + 1)

/-- The support idempotent for the diagonal `r = s` in the weight grid. -/
private noncomputable def diagonalSupportProjector (k : ℕ) :
    Matrix (WeightGrid k) (WeightGrid k) ℂ :=
  Matrix.diagonal (fun i : WeightGrid k =>
    if i.1 = i.2 then (1 : ℂ) else 0)

/-- The support idempotent for the anti-diagonal `r + s = k`. -/
private noncomputable def antiDiagonalSupportProjector (k : ℕ) :
    Matrix (WeightGrid k) (WeightGrid k) ℂ :=
  Matrix.diagonal (fun i : WeightGrid k =>
    if i.1.val + i.2.val = k then (1 : ℂ) else 0)

/--
Claim 7092: on the literal `(k+1) × (k+1)` weight grid, the diagonal and
anti-diagonal support projectors have rank `k+1`, and restricting the
reviewed torus action to them gives the two indicated characters.
-/
def diagonalAndAntiDiagonalAlignmentProjectors_claim7092 : Prop :=
  ∀ (k : ℕ) (y α : ℂ),
    y ≠ 0 → α ≠ 0 →
      (diagonalSupportProjector k).rank = k + 1 ∧
        (antiDiagonalSupportProjector k).rank = k + 1 ∧
        Matrix.trace
            (mixedHarmonicTorusAction k y α * diagonalSupportProjector k) =
          harmonicCharacter k (y * α) ∧
        Matrix.trace
            (mixedHarmonicTorusAction k y α * antiDiagonalSupportProjector k) =
          harmonicCharacter k (y / α)

end MathlibPlus.Open.Analysis.Claim7092
