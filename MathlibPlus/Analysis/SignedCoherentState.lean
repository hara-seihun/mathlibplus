import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MathlibPlus.Analysis.SignedCoherentState

/-- The folded density kernel at `a = 5/4` has the exact signed coherent-state
expansion from packet `C-0006`. -/
theorem foldedKernel_expansion (q u : ℝ) :
    Real.exp (-2 * ((5 : ℝ) / 4) * u - q * Real.exp (-2 * u)) +
        Real.exp (2 * ((5 : ℝ) / 4) * u - q * Real.exp (2 * u)) =
      2 * ∑' n : ℕ,
        (-q) ^ n / (n.factorial : ℝ) *
          Real.cosh (2 * ((n : ℝ) + (5 : ℝ) / 4) * u) := by
  let a : ℝ := 5 / 4
  have hpos :=
    (NormedSpace.expSeries_div_hasSum_exp (-q * Real.exp (2 * u))).mul_left
      (Real.exp (2 * a * u))
  have hneg :=
    (NormedSpace.expSeries_div_hasSum_exp (-q * Real.exp (-2 * u))).mul_left
      (Real.exp (-2 * a * u))
  have hpos' : HasSum
      (fun n : ℕ => (-q) ^ n / (n.factorial : ℝ) *
        Real.exp (2 * ((n : ℝ) + a) * u))
      (Real.exp (2 * a * u - q * Real.exp (2 * u))) := by
    have hp : HasSum
        (fun n : ℕ => (-q) ^ n / (n.factorial : ℝ) *
          Real.exp (2 * ((n : ℝ) + a) * u))
        (Real.exp (2 * a * u) * NormedSpace.exp (-q * Real.exp (2 * u))) :=
      hpos.congr_fun (fun n => by
      have hexp :
          Real.exp (2 * ((n : ℝ) + a) * u) =
            Real.exp (2 * a * u) * Real.exp ((n : ℝ) * (2 * u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp, mul_pow, ← Real.exp_nat_mul]
      ring)
    have hr :
        Real.exp (2 * a * u) * NormedSpace.exp (-q * Real.exp (2 * u)) =
          Real.exp (2 * a * u - q * Real.exp (2 * u)) := by
      rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
      congr 1
      ring
    rw [hr] at hp
    exact hp
  have hneg' : HasSum
      (fun n : ℕ => (-q) ^ n / (n.factorial : ℝ) *
        Real.exp (-2 * ((n : ℝ) + a) * u))
      (Real.exp (-2 * a * u - q * Real.exp (-2 * u))) := by
    have hn : HasSum
        (fun n : ℕ => (-q) ^ n / (n.factorial : ℝ) *
          Real.exp (-2 * ((n : ℝ) + a) * u))
        (Real.exp (-2 * a * u) * NormedSpace.exp (-q * Real.exp (-2 * u))) :=
      hneg.congr_fun (fun n => by
      have hexp :
          Real.exp (-2 * ((n : ℝ) + a) * u) =
            Real.exp (-2 * a * u) * Real.exp ((n : ℝ) * (-2 * u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp, mul_pow, ← Real.exp_nat_mul]
      ring)
    have hr :
        Real.exp (-2 * a * u) * NormedSpace.exp (-q * Real.exp (-2 * u)) =
          Real.exp (-2 * a * u - q * Real.exp (-2 * u)) := by
      rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
      congr 1
      ring
    rw [hr] at hn
    exact hn
  have hsum := hneg'.add hpos'
  rw [← hsum.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [Real.cosh_eq]
  simp only [a]
  ring

/-- For `q > 0`, multiplying the `n`th coefficient by `(-1)ⁿ` is strictly
positive. This records the claimed alternation of the coherent-state coefficients. -/
theorem coefficient_alternatingSign {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * ((-q) ^ n / (n.factorial : ℝ)) := by
  rw [neg_pow q n]
  have hsquare : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add]
    simp only [← two_mul, pow_mul, neg_one_sq, one_pow]
  calc
    (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * q ^ n / (n.factorial : ℝ)) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          (q ^ n / (n.factorial : ℝ)) := by ring
    _ = q ^ n / (n.factorial : ℝ) := by rw [hsquare, one_mul]
    _ > 0 := div_pos (pow_pos hq n) (by positivity)

end MathlibPlus.Analysis.SignedCoherentState
