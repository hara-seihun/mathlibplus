import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-! Formalization of admitted claim 24141 (R-0711). -/

/-- The crossed root-orbit state rectangle has the displayed projective defect;
if the defect vanishes over a domain, one of the two stated failure modes occurs. -/
theorem rootOrbitRectangleFactorization_claim24141
    {K : Type*} [CommRing K] [NoZeroDivisors K]
    (pA pB pC pD ν N H : K)
    (hpC : pC = pB * H) (hpD : pD = pA * H) :
    let Ω := (pA - ν) * (pC - N) - (pB - ν) * (pD - N)
    Ω = (pA - pB) * (ν * H - N) ∧
      (Ω = 0 → pA = pB ∨ N = ν * H) := by
  dsimp
  have hfactor :
      (pA - ν) * (pC - N) - (pB - ν) * (pD - N) =
        (pA - pB) * (ν * H - N) := by
    rw [hpC, hpD]
    ring
  constructor
  · exact hfactor
  · intro hΩ
    have hprod : (pA - pB) * (ν * H - N) = 0 := by
      rw [← hfactor]
      exact hΩ
    rcases mul_eq_zero.mp hprod with h | h
    · left
      exact sub_eq_zero.mp h
    · right
      exact (sub_eq_zero.mp h).symm

end MathlibPlus.Algebra
