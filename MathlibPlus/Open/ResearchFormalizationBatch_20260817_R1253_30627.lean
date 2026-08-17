import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d

noncomputable section

/-- The integer sextic used in the quadratic-factor step, with the parameter
allowed to range over all integers. -/
def repairGRat30627 (d : ℤ) : Polynomial ℚ :=
  Polynomial.X ^ 6 + Polynomial.C 3 * Polynomial.X ^ 5 +
    Polynomial.C 6 * Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 3 +
    Polynomial.C ((d : ℚ) + 4) * Polynomial.X ^ 2 +
    Polynomial.C ((d : ℚ) + 1) * Polynomial.X + Polynomial.C (d : ℚ) - 1

/-- A monic integral quadratic, viewed in the rational polynomial ring. -/
def repairQuadratic30627 (u v : ℤ) : Polynomial ℚ :=
  Polynomial.X ^ 2 + Polynomial.C (u : ℚ) * Polynomial.X +
    Polynomial.C (v : ℚ)

/-- The Record 8 quantities attached to `x^2+u*x+v`. -/
def repairU30627 (u : ℤ) : ℤ := u - 1

def repairV30627 (v : ℤ) : ℤ := v - 1

def repairN30627 (u v : ℤ) : ℤ :=
  repairU30627 u ^ 2 - repairU30627 u * repairV30627 v +
    repairV30627 v ^ 2

def repairT30627 (u v : ℤ) : ℤ :=
  repairU30627 u ^ 2 + repairU30627 u - 2 * repairV30627 v

/-- Claim 30627: the Record 8 divisibility and lower bound lead to the sole
quadratic candidate `x^2+1`, and the displayed remainder selects `d=2`. -/
def claim30627 : Prop :=
  (∀ d : ℤ,
    (repairGRat30627 d) %ₘ
        (Polynomial.X ^ 2 + 1 : Polynomial ℚ) =
      Polynomial.C ((d : ℚ) - 2) * Polynomial.X) ∧
    (∀ d : ℤ,
      (Polynomial.X ^ 2 + 1 : Polynomial ℚ) ∣ repairGRat30627 d ↔ d = 2) ∧
    (∀ (d u v : ℤ), 2 ≤ d →
      repairQuadratic30627 u v ∣ repairGRat30627 d →
      let U := repairU30627 u
      let V := repairV30627 v
      let N := repairN30627 u v
      let T := repairT30627 u v
      N = -U * (T * N + 1) ∧
        N ∣ U ∧
        ((3 : ℚ) / 4) * (U : ℚ) ^ 2 ≤ (N : ℚ) ∧
        (U = 1 ∨ U = -1) ∧
        U = -1 ∧ V = 0 ∧ u = 0 ∧ v = 1 ∧
        repairQuadratic30627 u v = Polynomial.X ^ 2 + 1)

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d
