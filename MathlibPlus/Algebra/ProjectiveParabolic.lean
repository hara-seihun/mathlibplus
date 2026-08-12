import Mathlib.Tactic

namespace MathlibPlus.Algebra.ProjectiveParabolic

/-- Claim 8544, equation (6) of packet K-0102.  The recurrence and the
source definitions of `F`, `ε`, and `ρ` are retained rather than assumed as
free scalar data. -/
theorem forcingIdentity_of_recurrence
    (zPrev z zNext α β c : ℝ)
    (hzPrev : 0 < zPrev) (hz : 0 < z) (hc : 0 < c)
    (hrec : zNext = α / c * z - (β / c) ^ 2 * zPrev) :
    let dPrev := z / zPrev - 1
    let d := zNext / z - 1
    let ε := α / c - 2
    let ρ := (β / c) ^ 2 - 1
    let F := zNext - 2 * z + zPrev
    d - dPrev / (1 + dPrev) = F / z ∧
      F / z = ε - ρ / (1 + dPrev) := by
  dsimp
  have hzPrev' : zPrev ≠ 0 := ne_of_gt hzPrev
  have hz' : z ≠ 0 := ne_of_gt hz
  have hc' : c ≠ 0 := ne_of_gt hc
  constructor
  · field_simp [hzPrev', hz']
    ring
  · rw [hrec]
    field_simp [hzPrev', hz', hc']
    ring

end MathlibPlus.Algebra.ProjectiveParabolic
