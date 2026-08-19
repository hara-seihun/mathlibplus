import MathlibPlus.Open.ResearchFormalization.OracleAreaDepthOneClaim61063

namespace MathlibPlus.Open.ResearchFormalization.R3533Claim47828

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.OracleAreaDepthOneClaim61063

noncomputable section

/-- The weight contributed by one depth-one sign atom to the nonconstant
    atom mass. -/
def nonconstantWeight47828 (w : ℝ) : SignStump (Fin 4) → ℝ
  | .constant _ => 0
  | .query _ negative positive => if negative = positive then 0 else w

/-- The exact area of one depth-one Boolean atom in the ranked-square
    convention: constants have area zero and a nonconstant stump has area one. -/
def depthOneAtomArea47828 (tree : SignStump (Fin 4)) : ℝ :=
  nonconstantWeight47828 1 tree

/-- The total nonconstant atom mass of a finite law of four-bit atoms. -/
def nonconstantAtomMass47828
    (weights : Fin m → ℝ) (trees : Fin m → SignStump (Fin 4)) : ℝ :=
  ∑ j : Fin m, nonconstantWeight47828 (weights j) (trees j)

/-- The expected depth-one atom area of the same finite law. -/
def expectedDepthOneArea47828
    (weights : Fin m → ℝ) (trees : Fin m → SignStump (Fin 4)) : ℝ :=
  ∑ j : Fin m, weights j * depthOneAtomArea47828 (trees j)

/-- The ordered four-coordinate quadratic area displayed in the claim. -/
def orderedDepthOneArea47828 (b : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, (i.val + 1 : ℝ) * (b i) ^ 2

/-- The actual finite-mixture carrier for the ordered affine coefficients:
    the coefficients are absolute aggregate stump coefficients in one
    coordinate order, and the packet's ordering and mass constraints are
    explicit hypotheses rather than hidden assumptions. -/
def depthOneAffineData47828
    (weights : Fin m → ℝ) (trees : Fin m → SignStump (Fin 4))
    (b : Fin 4 → ℝ) : Prop :=
  validMixture m weights ∧
    ∃ σ : Equiv.Perm (Fin 4),
      (∀ i : Fin 4,
        b i =
          |aggregateCoefficient m weights trees (σ i)|) ∧
        (∀ i : Fin 4, 0 ≤ b i) ∧
          (∀ i j : Fin 4, i.val ≤ j.val → b j ≤ b i) ∧
            (∑ i : Fin 4, b i) ≤ 1

/-- Claim 47828: for every finite four-bit Boolean atom law whose depth-one
    target has the displayed ordered absolute affine coefficients, the
    ranked quadratic area is bounded by total nonconstant mass times the
    coefficient mass, that product is at most the mass, and the expected
    atom area is the same mass. -/
def depthOneAffineCoefficientOne_claim47828 : Prop :=
  ∀ (m : ℕ) (weights : Fin m → ℝ)
    (trees : Fin m → SignStump (Fin 4)) (b : Fin 4 → ℝ),
    depthOneAffineData47828 weights trees b →
      orderedDepthOneArea47828 b ≤
          nonconstantAtomMass47828 weights trees * (∑ i : Fin 4, b i) ∧
        nonconstantAtomMass47828 weights trees * (∑ i : Fin 4, b i) ≤
          nonconstantAtomMass47828 weights trees ∧
          expectedDepthOneArea47828 weights trees =
            nonconstantAtomMass47828 weights trees ∧
            orderedDepthOneArea47828 b ≤
              expectedDepthOneArea47828 weights trees

end

end MathlibPlus.Open.ResearchFormalization.R3533Claim47828
