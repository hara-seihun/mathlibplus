import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MathlibPlus.Analysis

/-- Claim 53264's displayed Bernstein expansion for the cubic `P_r`. -/
theorem cubicGapBernsteinIdentity_53264 {r x : ℝ} (hr : 1 ≤ r) :
    let P : ℝ → ℝ := fun t =>
      3 * r ^ 3 - 3 * r ^ 3 * t + r * (r - 1) * (3 * r - 1) * t ^ 2 -
        2 * (r - 1) ^ 2 * (r + 1) * t ^ 3
    let b0 : ℝ := 3 * r ^ 3
    let b1 : ℝ := r ^ 3 * (2 * r + 3) / (r + 1)
    let b2 : ℝ := 2 * r ^ 3 * (3 * r ^ 2 + 4 * r + 5) /
      (3 * (r + 1) ^ 2)
    let b3 : ℝ := r ^ 3 * (r + 2) / (r + 1)
    P (r / (r + 1) * x) =
      b0 * (1 - x) ^ 3 + 3 * b1 * x * (1 - x) ^ 2 +
        3 * b2 * x ^ 2 * (1 - x) + b3 * x ^ 3 := by
  dsimp
  have hne : r + 1 ≠ 0 := by linarith
  field_simp [hne]
  ring

/-- The four Bernstein coefficients displayed in claim 53264 are positive on
its stated range `r ≥ 1`. -/
theorem cubicGapBernsteinCoefficientsPos_53264 {r : ℝ} (hr : 1 ≤ r) :
    0 < 3 * r ^ 3 ∧
      0 < r ^ 3 * (2 * r + 3) / (r + 1) ∧
      0 < 2 * r ^ 3 * (3 * r ^ 2 + 4 * r + 5) /
        (3 * (r + 1) ^ 2) ∧
      0 < r ^ 3 * (r + 2) / (r + 1) := by
  have hpoly : 0 < 3 * r ^ 2 + 4 * r + 5 := by
    nlinarith [sq_nonneg r]
  have h0 : 0 < 3 * r ^ 3 := by positivity
  have h1 : 0 < r ^ 3 * (2 * r + 3) / (r + 1) := by positivity
  have h2 : 0 < 2 * r ^ 3 * (3 * r ^ 2 + 4 * r + 5) /
      (3 * (r + 1) ^ 2) := by positivity
  have h3 : 0 < r ^ 3 * (r + 2) / (r + 1) := by positivity
  exact ⟨h0, h1, h2, h3⟩

/-- Positivity of the cubic certificate on the interval in claim 53264. -/
theorem cubicGapPolynomialPos_53264 {r t : ℝ}
    (hr : 1 ≤ r) (ht0 : 0 ≤ t) (ht_upper : t ≤ r / (r + 1)) :
    0 < 3 * r ^ 3 - 3 * r ^ 3 * t +
        r * (r - 1) * (3 * r - 1) * t ^ 2 -
        2 * (r - 1) ^ 2 * (r + 1) * t ^ 3 := by
  have hr0 : 0 < r := by linarith
  have hrp : 0 < r + 1 := by linarith
  let x : ℝ := t * (r + 1) / r
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hmul : t * (r + 1) ≤ r := (le_div_iff₀ hrp).mp ht_upper
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ hr0).2
    simpa using hmul
  have hcoeff := cubicGapBernsteinCoefficientsPos_53264 (r := r) hr
  rcases hcoeff with ⟨hb0, hb1, hb2, hb3⟩
  have hx1nonneg : 0 ≤ 1 - x := by linarith
  have hterm2 :
      0 ≤ 3 * (r ^ 3 * (2 * r + 3) / (r + 1)) * x * (1 - x) ^ 2 := by
    positivity
  have hterm3 :
      0 ≤ 3 * (2 * r ^ 3 * (3 * r ^ 2 + 4 * r + 5) /
        (3 * (r + 1) ^ 2)) * x ^ 2 * (1 - x) := by
    positivity
  have hterm4 : 0 ≤ (r ^ 3 * (r + 2) / (r + 1)) * x ^ 3 := by
    positivity
  have hbern :
      0 < (3 * r ^ 3) * (1 - x) ^ 3 +
        3 * (r ^ 3 * (2 * r + 3) / (r + 1)) * x * (1 - x) ^ 2 +
        3 * (2 * r ^ 3 * (3 * r ^ 2 + 4 * r + 5) /
          (3 * (r + 1) ^ 2)) * x ^ 2 * (1 - x) +
        (r ^ 3 * (r + 2) / (r + 1)) * x ^ 3 := by
    by_cases hxeq : x = 1
    · rw [hxeq]
      norm_num
      exact hb3
    · have hxlt : x < 1 := lt_of_le_of_ne hx1 (fun h => hxeq h)
      have hterm1 : 0 < (3 * r ^ 3) * (1 - x) ^ 3 := by
        positivity
      have hfirst :
          0 < (3 * r ^ 3) * (1 - x) ^ 3 +
            3 * (r ^ 3 * (2 * r + 3) / (r + 1)) * x * (1 - x) ^ 2 :=
        add_pos_of_pos_of_nonneg hterm1 hterm2
      have hfirst3 :
          0 < (3 * r ^ 3) * (1 - x) ^ 3 +
            3 * (r ^ 3 * (2 * r + 3) / (r + 1)) * x * (1 - x) ^ 2 +
            3 * (2 * r ^ 3 * (3 * r ^ 2 + 4 * r + 5) /
              (3 * (r + 1) ^ 2)) * x ^ 2 * (1 - x) :=
        add_pos_of_pos_of_nonneg hfirst hterm3
      exact add_pos_of_pos_of_nonneg hfirst3 hterm4
  have hidentity := cubicGapBernsteinIdentity_53264 (r := r) (x := x) hr
  dsimp at hidentity
  have hscale : r / (r + 1) * x = t := by
    dsimp [x]
    field_simp [ne_of_gt hr0, ne_of_gt hrp]
  rw [hscale] at hidentity
  rw [hidentity]
  exact hbern

end MathlibPlus.Analysis
