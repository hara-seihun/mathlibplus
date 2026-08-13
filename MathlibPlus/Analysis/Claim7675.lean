import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim7675

/-- The displayed passive-quartet polynomial, its positive fourth-power
energy, and the claimed negative derivative at `2`.  The real-variable
polynomial `P_Y` is kept separate from the complex polynomial `Y` exactly as
in the source display. -/
def passiveQuartetEnergyVeto : Prop :=
  let _Y : ℂ → ℂ := fun z => z ^ 4 + 6 * z ^ 2 + 25
  let P_Y : ℝ → ℝ := fun u => u ^ 2 - 6 * u + 25
  let energy : ℝ → ℝ := fun u => P_Y u ^ 4
  let h_Y : ℝ → ℝ := fun u => 2 * u * (u - 3) / P_Y u
  (∀ u, 0 ≤ energy u) ∧
    -deriv h_Y 2 = -(26 : ℝ) / 289 ∧
    -(26 : ℝ) / 289 < 0

end MathlibPlus.Analysis.Claim7675
