import MathlibPlus.Basic

namespace MathlibPlus.AlgebraicGeometry

/-!
Formalization of admitted claim 50486.  The quotient relation
`χ(O_X̂) = |G| * χ(O_S)` is made explicit so that the displayed values
`32` and `32` genuinely derive `χ(O_S) = 1`; the final identity is the
source's `χ(O_S) = 1 - q(S) + p_g(S)`.
-/

/-- The displayed quotient Euler characteristic and geometric-genus data force
    the irregularity to vanish. -/
theorem quotient_irregularity_zero_claim50486
    (chiX chiS groupDegree geometricGenus irregularity : ℤ)
    (hchiX : chiX = 32)
    (hdegree : groupDegree = 32)
    (hquotient : chiX = groupDegree * chiS)
    (hpg : geometricGenus = 0)
    (hchi : chiS = 1 - irregularity + geometricGenus) :
    irregularity = 0 := by
  have hquotient' := hquotient
  rw [hchiX, hdegree] at hquotient'
  have hS : chiS = 1 := by
    omega
  omega

end MathlibPlus.AlgebraicGeometry
