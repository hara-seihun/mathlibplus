import MathlibPlus.Basic

open scoped Matrix

namespace MathlibPlus.LinearAlgebra.Claim12212

/-- The off-diagonal coupling contributes exactly `2 c^2` to the second
power trace of the two-state matrix. -/
theorem coupledFiber_secondPowerTrace_claim12212
    {R : Type*} [CommRing R] (x c y : R) :
    Matrix.trace ((!![x, c; c, y] : Matrix (Fin 2) (Fin 2) R) ^ 2) =
      x ^ 2 + y ^ 2 + 2 * c ^ 2 := by
  simp [pow_two, Matrix.trace, Fin.sum_univ_succ]
  ring

/-- The mixed-word defect relative to the uncoupled diagonal trace. -/
theorem coupledFiber_mixedContribution_claim12212
    {R : Type*} [CommRing R] (x c y : R) :
    Matrix.trace ((!![x, c; c, y] : Matrix (Fin 2) (Fin 2) R) ^ 2) -
        (x ^ 2 + y ^ 2) = 2 * c ^ 2 := by
  rw [coupledFiber_secondPowerTrace_claim12212]
  ring

end MathlibPlus.LinearAlgebra.Claim12212
