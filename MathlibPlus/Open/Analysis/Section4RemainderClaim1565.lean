import Mathlib

namespace MathlibPlus.Open.Analysis.Section4Remainder

noncomputable section

/-- The first normalized remainder piece in the Section 4 propagation. -/
def firstRemainderPiece (α ω p z : ℝ) : ℝ :=
  Real.exp ((α - p) * z) * Real.rpow z (ω - 1)

/-- Its logarithm, on the positive half-line. -/
def firstRemainderLog (α ω p : ℝ) : ℝ → ℝ :=
  fun z => Real.log (firstRemainderPiece α ω p z)

/-- The logarithmic remainder piece with exponent `p=1`. -/
def logarithmicRemainderPiece (α ω z : ℝ) : ℝ :=
  Real.exp ((α - 1) * z) * Real.rpow z ω

/-- Its logarithm. -/
def logarithmicRemainderLog (α ω : ℝ) : ℝ → ℝ :=
  fun z => Real.log (logarithmicRemainderPiece α ω z)

/-- Claim 1565: the exact Section 4 logarithmic derivatives and their endpoint
monotonicity, specialized to the parameters displayed in the common-interval
reserve claim. -/
def section4RemainderMonotonicity_claim1565 : Prop :=
  let α : ℝ := 817 / 50000
  let ω : ℝ := 397 / 500
  (∀ p : ℝ, (p = 1 / 2 ∨ p = 2 / 3) →
    ∀ z : ℝ, 0 < z →
      deriv (firstRemainderLog α ω p) z =
          α - p + (ω - 1) / z ∧
        α - p + (ω - 1) / z ≤ 0 ∧
        AntitoneOn (firstRemainderPiece α ω p) (Set.Ioi 0)) ∧
    (∀ z : ℝ, 40 ≤ z →
      deriv (logarithmicRemainderLog α ω) z =
          α - 1 + ω / z ∧
        α - 1 + ω / z < 0 ∧
        AntitoneOn (logarithmicRemainderPiece α ω) (Set.Ici 40))

end
end MathlibPlus.Open.Analysis.Section4Remainder
