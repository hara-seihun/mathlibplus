import Mathlib

open Filter Topology

namespace MathlibPlus.Analysis.Claim15634

/--
For a positive real geometric parameter different from one, the powers have
exactly the two limiting behaviours stated in Claim 15634.  This is the
formal core of the source's assertion that a nontrivial parameter cannot stay
uniformly close to one along the full prime-power tower.
-/
theorem geometricPowerDichotomy_claim15634 (a : ℝ) (ha : 0 < a) (hane : a ≠ 1) :
    (a < 1 ∧ Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)) ∨
      (1 < a ∧ Tendsto (fun n : ℕ => a ^ n) atTop atTop) := by
  rcases lt_or_gt_of_ne hane with hlt | hgt
  · exact Or.inl ⟨hlt, tendsto_pow_atTop_nhds_zero_of_lt_one ha.le hlt⟩
  · exact Or.inr ⟨hgt, tendsto_pow_atTop_atTop_of_one_lt hgt⟩

end MathlibPlus.Analysis.Claim15634
