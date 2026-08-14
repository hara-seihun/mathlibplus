import Mathlib

namespace MathlibPlus.Open.Analysis.NR2RankTwo

private abbrev V := Fin 2 → ℝ

private def R_S : V := fun i => if i = 0 then 1 else 0
private def R_T : V := fun i => if i = 1 then 1 else 0
/-- Claim 19549: the two moving-basis values and their signed difference. -/
def claim19549 (Φ_X : V →ₗ[ℝ] ℝ) : Prop :=
  Φ_X R_S = 1 ∧ Φ_X R_T = -1 ∧ Φ_X (R_S - R_T) = 2 ∧ (2 : ℝ) ≠ 0

/-- Claim 19550: the square-shift functional does not factor through augmentation. -/
def claim19550 (Φ_X : V →ₗ[ℝ] ℝ) : Prop :=
  Φ_X R_S = 1 ∧ Φ_X R_T = -1 ∧
    (R_S - R_T) 0 + (R_S - R_T) 1 = 0 ∧
    Φ_X (R_S - R_T) = 2 ∧
    ¬ ∃ ψ : ℝ →ₗ[ℝ] ℝ, ∀ v : V, Φ_X v = ψ (v 0 + v 1)

/-- Claim 19551: exact expansion in the rank-two cup basis. -/
def claim19551 (v : V) : Prop :=
  v = (7 / 2 : ℝ) • R_S + (3 / 2 : ℝ) • R_T

end MathlibPlus.Open.Analysis.NR2RankTwo
