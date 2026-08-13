import Mathlib

namespace MathlibPlus.Algebra.Claim48877

/-- Arithmetic core of admitted claim 48877: the holomorphic Euler formula
specializes to `chi = 1` when both the geometric genus and irregularity vanish. -/
theorem tertiaryWitnessChiOne_core
    (chi pg q : ℤ)
    (hformula : chi = 1 - q + pg)
    (hpg : pg = 0) (hq : q = 0) :
    chi = 1 := by
  simpa [hpg, hq] using hformula

end MathlibPlus.Algebra.Claim48877
