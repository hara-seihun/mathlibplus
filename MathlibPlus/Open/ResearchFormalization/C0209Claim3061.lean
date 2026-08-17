import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.C0209

open MathlibPlus.Analysis.ReciprocalXi

/-- The original xi square-variable entire function from the source. -/
def xiSquareVariable (z : ℂ) : ℂ :=
  xi ((1 / 2 : ℂ) + Complex.sqrt z)

/-- The original xi coefficient sequence, expressed using the centered even
Taylor derivatives of the named xi function. -/
def xiCoefficient (n : ℕ) : ℝ :=
  (iteratedDeriv (2 * n)
      (fun z : ℂ => xi ((1 / 2 : ℂ) + z)) 0 /
      (Nat.factorial (2 * n) : ℂ)).re

def xiAlpha : ℝ := 1 / 4

def xiEndpointValue : ℝ :=
  (xiSquareVariable (xiAlpha : ℂ)).re

/-- The coefficient-series carrier for the original xi square-variable
function. -/
def xiCoefficientSeries : Prop :=
  ∀ z : ℂ,
    HasSum (fun n : ℕ => (xiCoefficient n : ℂ) * z ^ n)
      (xiSquareVariable z)

/-- The exact bilateral endpoint completion from the divided-difference
construction. -/
def xiEndpointTail (n : ℕ) : ℝ :=
  ∑' j : ℕ, xiCoefficient (n + 1 + j) * xiAlpha ^ j

def xiEndpointSequence (n : ℤ) : ℝ :=
  if _h : 0 ≤ n then xiEndpointTail n.toNat
  else xiEndpointValue * xiAlpha ^ ((-n).toNat - 1)

/-- The deleted-row maximal rank-two endpoint cofactor. -/
def xiEndpointDelta (k : ℕ) (m : Fin 3) : ℝ :=
  Matrix.det (fun i j : Fin 2 =>
    xiEndpointSequence
      ((k : ℤ) + (j.1 : ℤ) -
        ((Fin.succAbove m i).1 : ℤ)))

/-- The concrete positivity and scalar hypotheses for the original xi
coefficient sequence. -/
def xiEndpointScalarConditions : Prop :=
  xiAlpha > 0 ∧
    (∀ n : ℕ, 0 < xiCoefficient n) ∧
      (∀ n : ℕ, 1 ≤ n →
        xiCoefficient n ^ 2 >
          (((n + 1 : ℕ) : ℝ) / (n : ℝ)) *
            xiCoefficient (n - 1) * xiCoefficient (n + 1)) ∧
        let δ : ℝ := xiAlpha * xiCoefficient 1 / xiCoefficient 0
        δ ^ 2 + δ < 1 ∧
          2 * xiCoefficient 0 > xiEndpointValue

/-- Claim 3061: every shift of the original xi rank-two endpoint-completed
block has positive deleted-row cofactors and the two strict quarter
contractions. -/
def everyShiftRankTwoXiEndpointDominance : Prop :=
  xiCoefficientSeries ∧
    xiEndpointScalarConditions ∧
      ∀ k : ℕ, 1 ≤ k →
        (∀ m : Fin 3, 0 < xiEndpointDelta k m) ∧
          xiAlpha * xiEndpointDelta k 1 < xiEndpointDelta k 0 ∧
            xiAlpha * xiEndpointDelta k 2 < xiEndpointDelta k 1

end MathlibPlus.Open.ResearchFormalization.C0209
