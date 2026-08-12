import Mathlib

namespace MathlibPlus.Analysis

/-! Formalization of admitted claim 12714.  The source says “complex zero”, so
`_hρ` records the zero premise; “real” is represented by vanishing imaginary
part.  Self-adjoint eligibility is not separately formalized because no spectral
notion is specified in the claim. -/

/-- For a complex zeta zero, the displayed energy is real exactly on the
critical line. -/
theorem partition_zero_energy_real_iff (ρ : ℂ) (_hρ : riemannZeta ρ = 0) :
    (-Complex.I * (ρ - (1 / 2 : ℂ))).im = 0 ↔ ρ.re = 1 / 2 := by
  rw [Complex.mul_im]
  simp
  ring_nf
  constructor <;> intro h <;> linarith

end MathlibPlus.Analysis
