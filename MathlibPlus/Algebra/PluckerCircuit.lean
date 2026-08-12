import Mathlib

namespace MathlibPlus.Algebra.PluckerCircuit

/-- The four-factor Plücker circuit from admitted claim 56841 is an
identity in every commutative ring, before any evaluation or truncation. -/
theorem fourFactorPluckerCircuit {R : Type*} [CommRing R]
    (F_a F_b F_c F_d : R) :
    (F_a - F_b) * (F_c - F_d)
        - (F_a - F_c) * (F_b - F_d)
        + (F_a - F_d) * (F_b - F_c) = 0 := by
  ring

end MathlibPlus.Algebra.PluckerCircuit
