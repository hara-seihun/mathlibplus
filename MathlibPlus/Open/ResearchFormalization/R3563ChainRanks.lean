import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3563ChainRanks

private abbrev C0 := Fin 1 → ℚ
private abbrev C1 := Fin 2 → ℚ
private abbrev C2 := Fin 2 → ℚ
private abbrev C3 := Fin 1 → ℚ

private def delta0Matrix : Matrix (Fin 2) (Fin 1) ℚ := 0
private def delta1Matrix : Matrix (Fin 2) (Fin 2) ℚ := 0
private def delta2Matrix : Matrix (Fin 1) (Fin 2) ℚ := !![1, 0]

private def delta0 : C0 →ₗ[ℚ] C1 := Matrix.toLin' delta0Matrix
private def delta1 : C1 →ₗ[ℚ] C2 := Matrix.toLin' delta1Matrix
private def delta2 : C2 →ₗ[ℚ] C3 := Matrix.toLin' delta2Matrix

/-- Claim 50748: the displayed rational cochain maps form the stated chain
complex and have ranks zero, zero, and one. -/
def claim50748_chainIdentitiesAndRanks : Prop :=
  delta1.comp delta0 = 0 ∧
    delta2.comp delta1 = 0 ∧
      Module.finrank ℚ (LinearMap.range delta0) = 0 ∧
        Module.finrank ℚ (LinearMap.range delta1) = 0 ∧
          Module.finrank ℚ (LinearMap.range delta2) = 1

end MathlibPlus.Open.ResearchFormalization.R3563ChainRanks
