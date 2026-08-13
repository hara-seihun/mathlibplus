import Mathlib

namespace MathlibPlus.Analysis.Claim7212

/-- The exact algebraic Radau identity, with the derivative product rules and
nonvanishing denominators exposed as hypotheses. -/
theorem exactRadauIdentity_claim7212
    (z Q R G E Q' R' G' E' ρ : ℂ)
    (hE : E = Q - R * G)
    (hE' : E' = Q' - R' * G - R * G')
    (hρ : ρ = -z * G' / G)
    (hG : G ≠ 0)
    (hden : Q - E ≠ 0) :
    R * Q * ρ - z * (Q * R' - R * Q') =
      z * R * (Q * E' - E * Q') / (Q - E) := by
  rw [hρ, hE, hE']
  have hden' : R * G ≠ 0 := by
    intro hRG
    apply hden
    rw [hE, hRG]
    ring
  have hR : R ≠ 0 := by
    intro hR
    apply hden'
    simp [hR]
  simp only [sub_sub_cancel]
  field_simp [hG, hR, hden']
  ring

end MathlibPlus.Analysis.Claim7212
