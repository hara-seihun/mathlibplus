import MathlibPlus.Open.Research.FormalizationBatch_01a00bf2_OrthogonalReflectionCompression

namespace MathlibPlus.Open.Research.FormalizationBatch_01a00bf2

noncomputable section

/-- The simultaneous `(R_h,R_c)=(ε,η)` eigenspace on the actual mixed
coefficient carrier. -/
def jointEigenspace (k : ℕ) (b : WeightBasis k) (ε η : ℂ) :
    Submodule ℂ (M k) :=
  (LinearMap.ker
      ((leftReversal k b) +
        (-1 : ℂ) • (ε • (LinearMap.id : M k →ₗ[ℂ] M k)))) ⊓
    (LinearMap.ker
      ((rightReversal k b) +
        (-1 : ℂ) • (η • (LinearMap.id : M k →ₗ[ℂ] M k))))

/-- The projector onto the joint eigenspace with signs `ε,η`. -/
def jointProjector (k : ℕ) (b : WeightBasis k) (ε η : ℂ) :
    M k →ₗ[ℂ] M k :=
  ((4 : ℂ)⁻¹) •
    ((mixedIdentity k b + ε • leftReversal k b).comp
      (mixedIdentity k b + η • rightReversal k b))

/-- The exact finite heat operator `𝒦_λ`. -/
def heatOperator (k : ℕ) (b : WeightBasis k) (rho : ℂ) :
    M k →ₗ[ℂ] M k :=
  ((4 : ℂ)⁻¹) •
    ((1 + rho) • (mixedIdentity k b + longestOperator k b) +
      (1 + (-1 : ℂ) • rho) • (leftReversal k b + rightReversal k b))

/-- The balanced inverse on the Arthur range at `λ=1/2`. -/
def balancedHeatPseudoinverse (k : ℕ) (b : WeightBasis k) :
    M k →ₗ[ℂ] M k :=
  jointProjector k b 1 1 + 2 • jointProjector k b (-1) (-1)

/-- Operator rank means the dimension of its actual image. -/
def operatorRank {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) : ℕ :=
  Module.finrank ℂ (LinearMap.range A)

/-- The balanced joint-eigenspace dimensions and the balanced pseudoinverse
identity for the heat operator on `Sym^k(ℂ²) ⊗ Sym^k(ℂ²)`. -/
def heatEigenspaceDimensionsAndBalancedPseudoinverse : Prop :=
  ∀ (k : ℕ) (b : WeightBasis k),
    let a : ℕ := (k + 2) / 2
    let c : ℕ := (k + 1) / 2
    let Epp := jointEigenspace k b 1 1
    let Epm := jointEigenspace k b 1 (-1)
    let Emp := jointEigenspace k b (-1) 1
    let Emm := jointEigenspace k b (-1) (-1)
    let Pi := arthurProjector k b
    let Kplus := balancedHeatPseudoinverse k b
    Module.finrank ℂ Epp = a ^ 2 ∧
      Module.finrank ℂ Epm = a * c ∧
      Module.finrank ℂ Emp = a * c ∧
      Module.finrank ℂ Emm = c ^ 2 ∧
      operatorRank Pi = a ^ 2 + c ^ 2 ∧
      Kplus = jointProjector k b 1 1 + 2 • jointProjector k b (-1) (-1) ∧
      Kplus = ((4 : ℂ)⁻¹) •
        (3 • mixedIdentity k b + (-1 : ℂ) • leftReversal k b +
          (-1 : ℂ) • rightReversal k b + 3 • longestOperator k b) ∧
      (heatOperator k b ((1 : ℂ) / 2)).comp Kplus = Pi

end
end MathlibPlus.Open.Research.FormalizationBatch_01a00bf2
