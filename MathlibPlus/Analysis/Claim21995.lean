import Mathlib

namespace MathlibPlus.Analysis

open Complex

/-- The reflected selected-source exponent identity from the fixed R-0487 slice. -/
theorem reflectedSelectedSourceExponentIdentity_claim21995
    (x : ℝ) (α : ℂ → ℂ)
    (hα : α (star ((1 + (31 / 100 : ℂ) - Complex.I * (x : ℂ)) / 2)) =
      star (α ((1 + (31 / 100 : ℂ) - Complex.I * (x : ℂ)) / 2))) :
    let t : ℂ := (1037 : ℂ) / 20000
    let y : ℂ := 31 / 100
    let sm : ℂ := (1 - y + Complex.I * (x : ℂ)) / 2
    let sp : ℂ := (1 + y - Complex.I * (x : ℂ)) / 2
    let ss : ℂ := sp + (t / 2) * α sp
    let κ : ℂ := (t / 2) * (α sm - α (star sp))
    let dual : ℂ := star ss + κ
    dual - y = sm + (t / 2) * α sm := by
  dsimp
  simp only [map_add, map_mul, starRingEnd_apply]
  rw [hα]
  simp
  ring

end MathlibPlus.Analysis
