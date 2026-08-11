import Mathlib

/-!
# Quadratic Jensen detection for the bare multiplier

The displayed multiplier in admitted claim 18810 is
`H_q(w) = 1 + q cosh (L sqrt w)`.  Its degree-two Jensen section has
`b₀ = 1 + q`, `b₁ = q L² / 2!`, and `b₂ = q L⁴ / 4!`; the definitions below
use exactly that displayed section, so `2 b₁ = q L²`.
-/

namespace MathlibPlus.Analysis

/-- The exact displayed quadratic Jensen section. -/
noncomputable def bareMultiplierJensen (L q w : ℝ) : ℝ :=
  1 + q + q * L ^ 2 * w + (q * L ^ 4 / 24) * w ^ 2

/-- Real factorization is the quadratic notion of hyperbolicity used here. -/
def bareMultiplierJensenHyperbolic (L q : ℝ) : Prop :=
  ∃ r s : ℝ, ∀ w : ℝ,
    bareMultiplierJensen L q w =
      (q * L ^ 4 / 24) * (w - r) * (w - s)

/-- The exact discriminant calculation from claim 18810. -/
theorem bareMultiplierJensen_discriminant (L q : ℝ) :
    (q * L ^ 2 / 2) ^ 2 - (1 + q) * (q * L ^ 4 / 24) =
      q * L ^ 4 / 24 * (5 * q - 1) := by
  ring

/-- For a nonzero `L` and `0 < q < 1/5`, the displayed quadratic section is
not hyperbolic. -/
theorem bareMultiplierJensen_not_hyperbolic_claim18810
    {L q : ℝ} (hL : L ≠ 0) (hq : 0 < q) (hsmall : q < 1 / 5) :
    ¬ bareMultiplierJensenHyperbolic L q := by
  intro h
  rcases h with ⟨r, s, hs⟩
  let b2 : ℝ := q * L ^ 4 / 24
  have hb2 : 0 < b2 := by
    dsimp [b2]
    positivity
  have h0 := hs 0
  have h1 := hs 1
  have hm1 := hs (-1)
  have hcoef0 : 1 + q = b2 * (r * s) := by
    dsimp [bareMultiplierJensen, b2] at h0 ⊢
    nlinarith
  have hcoef1 : q * L ^ 2 = -b2 * (r + s) := by
    dsimp [bareMultiplierJensen, b2] at h1 hm1 ⊢
    nlinarith
  have hdisc : 0 ≤ (q * L ^ 2 / 2) ^ 2 - (1 + q) * b2 := by
    calc
      (q * L ^ 2 / 2) ^ 2 - (1 + q) * b2 =
          (b2 ^ 2 / 4) * (r - s) ^ 2 := by
            rw [hcoef0, hcoef1]
            ring
      _ ≥ 0 := by positivity
  rw [bareMultiplierJensen_discriminant] at hdisc
  have hfactor : 0 < q * L ^ 4 / 24 := by positivity
  have hneg : q * L ^ 4 / 24 * (5 * q - 1) < 0 := by
    exact mul_neg_of_pos_of_neg hfactor (by nlinarith)
  exact (not_le_of_gt hneg) hdisc

end MathlibPlus.Analysis
