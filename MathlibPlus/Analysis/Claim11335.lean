import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim11335

/-- The scaled two-zero endpoint difference factors through the certificate
polynomial.  All quantities that Record 10 leaves in its surrounding context
are displayed here explicitly. -/
theorem endpoint_reserve_factorization
    (a g x : ℝ) (ha : 0 < a) (hg : 0 < g)
    (hx0 : 0 ≤ x) (hxg : x ≤ g) :
    let P : ℝ → ℝ → ℝ := fun p w =>
      2 * p ^ 8 + p ^ 6 * (8 - 6 * w) +
        p ^ 4 * (6 - 9 * w + 6 * w ^ 2) +
        p ^ 2 * (2 * w + 8 * w ^ 2 - 2 * w ^ 3) +
        w - 2 * w ^ 2 - 3 * w ^ 3
    let R₂ : ℝ → ℝ → ℝ → ℝ := fun a g x =>
      x ^ 2 / (a ^ 2 + x ^ 2) ^ 2 +
        (g - x) ^ 2 / (a ^ 2 + (g - x) ^ 2) ^ 2 +
        2 * a ^ 2 / ((a ^ 2 + x ^ 2) * (a ^ 2 + (g - x) ^ 2))
    let E : ℝ → ℝ → ℝ := fun a g =>
      (3 * g ^ 2 + 2 * a ^ 2) / (a ^ 2 + g ^ 2) ^ 2
    let p : ℝ := a / g
    let u : ℝ := x / g
    let w : ℝ := u * (1 - u)
    let den : ℝ :=
      (1 + p ^ 2) ^ 2 * (p ^ 2 + u ^ 2) ^ 2 *
        (p ^ 2 + (1 - u) ^ 2) ^ 2
    0 < den ∧
      g ^ 2 * (R₂ a g x - E a g) = u * (1 - u) * P p w / den := by
  have hax : 0 < a ^ 2 + x ^ 2 := by positivity
  have hgx : 0 < a ^ 2 + (g - x) ^ 2 := by positivity
  have hag : 0 < a ^ 2 + g ^ 2 := by positivity
  have hp : 0 < a / g := div_pos ha hg
  have hu : 0 ≤ x / g := div_nonneg hx0 (le_of_lt hg)
  have hgu : 0 ≤ 1 - x / g := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hg).mpr
    simpa using hxg
  have hden1 : 0 < 1 + (a / g) ^ 2 := by positivity
  have hden2 : 0 < (a / g) ^ 2 + (x / g) ^ 2 := by positivity
  have hden3 : 0 < (a / g) ^ 2 + (1 - x / g) ^ 2 := by positivity
  dsimp
  constructor
  · positivity
  · field_simp [ne_of_gt hax, ne_of_gt hgx, ne_of_gt hag,
      ne_of_gt hden1, ne_of_gt hden2, ne_of_gt hden3, ne_of_gt hg]
    ring

/-- The polynomial factor in the endpoint certificate is nonnegative on its
stated rectangle. -/
theorem endpointPolynomial_nonneg {p w : ℝ}
    (_hp : 0 ≤ p) (hw0 : 0 ≤ w) (hw4 : w ≤ 1 / 4) :
    0 ≤
      2 * p ^ 8 + p ^ 6 * (8 - 6 * w) +
        p ^ 4 * (6 - 9 * w + 6 * w ^ 2) +
        p ^ 2 * (2 * w + 8 * w ^ 2 - 2 * w ^ 3) +
        w - 2 * w ^ 2 - 3 * w ^ 3 := by
  have hw1 : w ≤ 1 := by linarith
  have hwsq : w ^ 2 ≤ w := by
    have hmul : 0 ≤ w * (1 - w) :=
      mul_nonneg hw0 (sub_nonneg.mpr hw1)
    nlinarith
  have hcoef1 : 0 ≤ 8 - 6 * w := by linarith
  have hcoef2 : 0 ≤ 6 - 9 * w + 6 * w ^ 2 := by
    nlinarith [sq_nonneg w]
  have hcoef3 : 0 ≤ 1 + 4 * w - w ^ 2 := by
    nlinarith
  have hterm3 : 0 ≤ 2 * w + 8 * w ^ 2 - 2 * w ^ 3 := by
    have hmul : 0 ≤ (2 * w) * (1 + 4 * w - w ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) hw0) hcoef3
    nlinarith
  have hcoef4 : 0 ≤ 1 - 3 * w := by linarith
  have hterm4 : 0 ≤ w - 2 * w ^ 2 - 3 * w ^ 3 := by
    have hmul : 0 ≤ w * (1 + w) * (1 - 3 * w) := by
      exact mul_nonneg (mul_nonneg hw0 (by linarith)) hcoef4
    nlinarith
  have h8 : 0 ≤ 2 * p ^ 8 := by positivity
  have h6 : 0 ≤ p ^ 6 * (8 - 6 * w) :=
    mul_nonneg (by positivity) hcoef1
  have h4 : 0 ≤ p ^ 4 * (6 - 9 * w + 6 * w ^ 2) :=
    mul_nonneg (by positivity) hcoef2
  have h2 : 0 ≤ p ^ 2 * (2 * w + 8 * w ^ 2 - 2 * w ^ 3) :=
    mul_nonneg (by positivity) hterm3
  nlinarith

end MathlibPlus.Analysis.Claim11335
