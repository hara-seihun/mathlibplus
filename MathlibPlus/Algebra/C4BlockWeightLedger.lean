import Mathlib

namespace MathlibPlus.Algebra

/-- The four cyclic edge sums of the inverse-paired vertex ledger
`(a, b, -b, -a)` are `(a+b, 0, -(a+b), 0)`. -/
theorem c4BlockWeightLedger (a b : ℝ) :
    let vertex : Fin 4 → ℝ := ![a, b, -b, -a]
    let edge : Fin 4 → ℝ :=
      ![vertex 0 + vertex 1, vertex 1 + vertex 2,
        vertex 2 + vertex 3, vertex 3 + vertex 0]
    edge = ![a + b, 0, -(a + b), 0] := by
  dsimp
  funext i
  fin_cases i <;> simp <;> ring

end MathlibPlus.Algebra
