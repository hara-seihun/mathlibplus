import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Real.Sqrt

open Filter
open scoped ENNReal Topology

namespace MathlibPlus.Analysis.CoordinateProjection

/-- Claim 15499: the rank-one coordinate projections on `ℓ²` converge
strongly to zero, and their norm at a vector is the norm of that coordinate. -/
theorem coordinateProjection_strongly_tendsto_zero
    {E : Type*} [NormedAddCommGroup E]
    (x : lp (fun _ : ℕ => E) (2 : ℝ≥0∞)) :
    (Tendsto (fun j => ‖lp.single (E := fun _ : ℕ => E) (2 : ℝ≥0∞) j
      ((x : ℕ → E) j)‖) atTop (𝓝 0)) ∧
      (∀ j, ‖lp.single (E := fun _ : ℕ => E) (2 : ℝ≥0∞) j
        ((x : ℕ → E) j)‖ = ‖((x : ℕ → E) j)‖) := by
  have hp : (0 : ℝ≥0∞) < 2 := by norm_num
  have hsum : Summable (fun j => ‖((x : ℕ → E) j)‖ ^ (2 : ℝ)) := by
    have hm : Memℓp (x : ℕ → E) (2 : ℝ≥0∞) := lp.memℓp x
    exact (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hm
  have hpow : Tendsto (fun j => ‖((x : ℕ → E) j)‖ ^ (2 : ℝ)) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  have hroot : Tendsto (fun j => Real.sqrt (‖((x : ℕ → E) j)‖ ^ (2 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hpow)
  have hnorm : Tendsto (fun j => ‖((x : ℕ → E) j)‖) atTop (𝓝 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hroot
  constructor
  · simpa only [lp.norm_single hp] using hnorm
  · intro j
    exact lp.norm_single (E := fun _ : ℕ => E) hp j ((x : ℕ → E) j)

end MathlibPlus.Analysis.CoordinateProjection
