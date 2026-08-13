import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The explicit three-dimensional `𝔽₅` module used as the empty-spectrum
`8T7` control has neither fixed nor anti-fixed vectors for either displayed
regular order-eight generator. -/
def eightT7F5EmptySpectrumModuleExcludesMarkedHallEigenlines : Prop :=
  let s : Matrix (Fin 3) (Fin 3) (ZMod 5) := fun i j =>
    ![![3, 1, 0], ![3, 0, 1], ![1, 0, 0]] i j
  let t : Matrix (Fin 3) (Fin 3) (ZMod 5) := fun i j =>
    ![![1, 1, 1], ![2, 0, 4], ![2, 0, 2]] i j
  (∀ v : Fin 3 → ZMod 5, s.mulVec v = v → v = 0) ∧
  (∀ v : Fin 3 → ZMod 5, s.mulVec v = -v → v = 0) ∧
  (∀ v : Fin 3 → ZMod 5, t.mulVec v = v → v = 0) ∧
  (∀ v : Fin 3 → ZMod 5, t.mulVec v = -v → v = 0)

end MathlibPlus.Open.GraphTheory
