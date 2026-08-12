import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim45575

/-- The two pushed six-coordinate columns in claim 45575 are distinct; their
coordinatewise difference is nonzero.  The source quotient-coordinate
identification is retained as an explicit fidelity boundary. -/
theorem pushedColumnDifference :
    let p₀ : Fin 6 → ℤ := ![1, 1, 1, 1, 0, 0]
    let p₄ : Fin 6 → ℤ := ![1, 1, 0, 0, 1, 1]
    p₀ ≠ p₄ ∧ p₀ 2 - p₄ 2 = 1 := by
  decide

end MathlibPlus.LinearAlgebra.Claim45575
