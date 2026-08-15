import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 18344: the rank-one skew displacement law. -/
def rankOneSkewDisplacementLaw (n : ℕ)
    (Z Ω : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  Z.transpose * Ω - Ω * Z =
    (-2 : ℝ) • (fun i j => c i * c j)

end MathlibPlus.Open.ResearchFormalization
