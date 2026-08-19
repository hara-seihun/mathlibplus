import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a000fa

namespace MathlibPlus.Open.ResearchFormalization.R3684Claim47825

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a000fa

/-- The two roots of the centred Euler pair, with the reviewed real-rpow
    normalization retained as the second component. -/
def centeredEulerRootPair47825 (p : ℕ) : ℝ × ℝ :=
  (Real.sqrt (p : ℝ), CenteredEulerPair.inverseSqrt p)

/-- The reciprocal polynomial read from the centred Euler root pair. -/
def centeredEulerReciprocalPolynomial47825 (p : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ 2 -
      Polynomial.C
        ((centeredEulerRootPair47825 p).1 +
          (centeredEulerRootPair47825 p).2) * Polynomial.X + 1

/-- The local companion polynomial uses the physical coefficient after the
    packet's `b / sqrt(p)` normalization. -/
def physicalQuadratic47825 (p : ℕ) (b : ℤ) : Polynomial ℝ :=
  Polynomial.X ^ 2 +
      Polynomial.C ((b : ℝ) / Real.sqrt (p : ℝ)) * Polynomial.X + 1

/-- The actual rank-two local companion matrix in that physical convention. -/
def localCompanion47825 (p : ℕ) (b : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), -1; 1, -((b : ℝ) / Real.sqrt (p : ℝ))]

/-- Read the physical parameter back from the lower-right companion entry. -/
def physicalCoefficient47825
    (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  -Real.sqrt (p : ℝ) * M 1 1

/-- Claim 47825: the actual centred Euler reciprocal polynomial factors at
    the two displayed roots, while exact matching in the separately named
    physical companion convention gives the distinct integer coefficient
    `b_p = -(p+1)`. -/
def centeredEulerPairAndPhysicalCoefficient_claim47825 : Prop :=
  ∀ p : ℕ, 1 < p →
    let roots := centeredEulerRootPair47825 p
    let E := centeredEulerReciprocalPolynomial47825 p
    let b : ℤ := -((p : ℤ) + 1)
    roots.2 = roots.1⁻¹ ∧
      E =
        (Polynomial.X - Polynomial.C roots.1) *
          (Polynomial.X - Polynomial.C roots.2) ∧
        physicalQuadratic47825 p b = E ∧
          physicalCoefficient47825 p (localCompanion47825 p b) = (b : ℝ) ∧
            b = -((p : ℤ) + 1)

end

end MathlibPlus.Open.ResearchFormalization.R3684Claim47825
