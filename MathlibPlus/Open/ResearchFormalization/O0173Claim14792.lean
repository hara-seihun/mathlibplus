import MathlibPlus.Open.Representation.MassCovarianceClaim14793

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0173Claim14792

noncomputable section

abbrev ClassSpace := MathlibPlus.Open.Representation.MassCovarianceClaim14793.ClassSpace
abbrev CoefficientMatrix := Matrix (Fin 2) (Fin 2) ℂ

open MathlibPlus.Open.Representation.MassCovarianceClaim14793

def massTensorContraction (V_N : ℝ) (B : CoefficientMatrix) :
    ClassSpace → ClassSpace :=
  fun x =>
    ∑ i : Fin 2,
      (∑ j : Fin 2,
        B i j * massBeta V_N (massBasis V_N j) x) • massBasis V_N i

def starProduct (B C : CoefficientMatrix) : CoefficientMatrix :=
  fun i j => ∑ k : Fin 2, B i k * C k j

def classTensorProductAlgebra : Prop :=
  ∀ (V_N : ℝ),
    0 < V_N →
      (∀ v : ClassSpace,
        ∃ a b : ℂ,
          v = a • massBasis V_N 0 + b • massBasis V_N 1) ∧
      massBeta V_N (massBasis V_N 0) (massBasis V_N 0) = 1 ∧
      massBeta V_N (massBasis V_N 0) (massBasis V_N 1) = 0 ∧
      massBeta V_N (massBasis V_N 1) (massBasis V_N 0) = 0 ∧
      massBeta V_N (massBasis V_N 1) (massBasis V_N 1) = 1 ∧
      (∀ B : CoefficientMatrix,
        coefficientMatrix V_N (massTensorContraction V_N B) = B) ∧
      (∀ B C : CoefficientMatrix,
        ∀ x : ClassSpace,
          massTensorContraction V_N (starProduct B C) x =
            massTensorContraction V_N B
              (massTensorContraction V_N C x)) ∧
      (∀ B C : CoefficientMatrix, ∀ i j : Fin 2,
        starProduct B C i j = ∑ k : Fin 2, B i k * C k j)

/-- The named E₁₂, √V_N Δ mass-whitened tensors contract to End(𝒞), and
composition is the ordinary coefficient-matrix product. -/
def claim14792 : Prop :=
  classTensorProductAlgebra

end

end MathlibPlus.Open.ResearchFormalization.O0173Claim14792
