import Mathlib

namespace MathlibPlus.Analysis.Claim55380

/-- The real first-collision projector `H + i H' / p` vanishes exactly at a
simultaneous zero of a real collision sum and its derivative. -/
theorem firstCollisionProjector_zero_iff_claim55380
    {p h dh : ℝ} (hp : p ≠ 0) :
    (h : ℂ) + Complex.I * (dh : ℂ) / (p : ℂ) = 0 ↔
      h = 0 ∧ dh = 0 := by
  constructor
  · intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    have hzero : h = 0 := by simpa using hre
    have dhzero : dh = 0 := by
      have hdiv : (dh : ℂ) / (p : ℂ) = 0 := by
        simpa [hzero] using him
      have hmul : (dh : ℂ) = 0 := (div_eq_zero_iff).mp hdiv |>.resolve_right hp0
      exact_mod_cast hmul
    exact ⟨hzero, dhzero⟩
  · rintro ⟨rfl, rfl⟩
    simp

end MathlibPlus.Analysis.Claim55380
