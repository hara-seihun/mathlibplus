import MathlibPlus.Basic

namespace MathlibPlus.AlgebraicGeometry.Claim46908

/-- The displayed smooth-locus and singular-point arithmetic from claim 46908. -/
def cTwo : ℤ := 7 * 0 + 3

def chiStructure : ℤ := 1 - 0 + 0

def cOneSquared : ℤ := 12 - cTwo

theorem invariantArithmetic :
    cTwo = 3 ∧ chiStructure = 1 ∧ cOneSquared = 9 := by
  norm_num [cTwo, chiStructure, cOneSquared]

/-- The three singular points contribute exactly three to `c₂` when the
smooth-locus Euler value is zero. -/
theorem cTwo_from_smooth_locus :
    7 * (0 : ℤ) + 3 = cTwo := by
  rfl

/-- Noether's displayed numerical substitution. -/
theorem noether_substitution :
    12 - cTwo = 9 := by
  norm_num [cTwo]

end MathlibPlus.AlgebraicGeometry.Claim46908
