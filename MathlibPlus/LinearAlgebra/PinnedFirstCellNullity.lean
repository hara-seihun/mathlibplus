import Mathlib

namespace MathlibPlus
namespace LinearAlgebra

/-- Exact arithmetic and the corresponding universal finite-dimensional nullity
bound in the first-cell parameters of claim 58129. -/
theorem pinnedFirstCellNullity_claim58129 :
    let K : ℕ := 690988
    let P : ℕ := 8192
    let R : ℕ := K * P
    let m : ℕ := 32768
    R = 5660573696 ∧
      R = m * 172747 ∧
      ∀ q : ℕ, q ≤ 172745 →
        R - m * (q + 1) ≥ 32768 ∧
        ∀ f : (Fin R → ℚ) →ₗ[ℚ] (Fin (m * (q + 1)) → ℚ),
          32768 ≤ Module.finrank ℚ (LinearMap.ker f) := by
  dsimp
  constructor
  · norm_num
  constructor
  · norm_num
  · intro q hq
    constructor
    · omega
    · intro f
      have hrank := LinearMap.finrank_range_add_finrank_ker f
      have hcod := (LinearMap.range f).finrank_le
      rw [Module.finrank_fin_fun] at hrank
      rw [Module.finrank_fin_fun] at hcod
      omega

end LinearAlgebra
end MathlibPlus
