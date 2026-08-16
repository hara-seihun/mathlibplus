import MathlibPlus.Open.FormalizationBatch.Claims7774And7880

namespace MathlibPlus.Open.RepresentationTheory

noncomputable section

/-- The polarized monomial model of `Sym^k (ℂ²)` used for the coefficient module. -/
abbrev CoefficientSymPower (k : ℕ) :=
  MathlibPlus.Open.FormalizationBatch.PolarizedSymmetricPower k

/-- The mixed coefficient module `Sym^k(ℂ²) ⊗ Sym^k(ℂ²)`. -/
abbrev CoefficientMixedSpace (k : ℕ) :=
  TensorProduct ℂ (CoefficientSymPower k) (CoefficientSymPower k)

/-- Swapping the two variables in a binary monomial. -/
def binaryReversal : Fin 2 ≃ Fin 2 := Fin.revPerm

/-- The reversal `J_k` on the monomial realization of the symmetric power. -/
def coefficientReversal (k : ℕ) :
    CoefficientSymPower k →ₗ[ℂ] CoefficientSymPower k :=
  Finsupp.lmapDomain ℂ ℂ (Sym.map binaryReversal)

/-- The factor-swap operator `S` on the mixed coefficient module. -/
def coefficientFactorSwap (k : ℕ) :
    CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k :=
  (TensorProduct.comm ℂ (CoefficientSymPower k) (CoefficientSymPower k)).toLinearMap

/-- The left-factor reversal `J_k ⊗ I`. -/
def coefficientLeftReversal (k : ℕ) :
    CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k :=
  TensorProduct.map (coefficientReversal k) (LinearMap.id :
    CoefficientSymPower k →ₗ[ℂ] CoefficientSymPower k)

/-- The right-factor reversal `I ⊗ J_k`. -/
def coefficientRightReversal (k : ℕ) :
    CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k :=
  TensorProduct.map (LinearMap.id :
    CoefficientSymPower k →ₗ[ℂ] CoefficientSymPower k) (coefficientReversal k)

/-- The simultaneous reversal `J_k ⊗ J_k`. -/
def coefficientDoubleReversal (k : ℕ) :
    CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k :=
  TensorProduct.map (coefficientReversal k) (coefficientReversal k)

/-- The tensor-product basis induced by the monomial coefficient bases. -/
def coefficientMixedBasis (k : ℕ) :
    Module.Basis (Sym (Fin 2) k × Sym (Fin 2) k) ℂ (CoefficientMixedSpace k) := by
  exact (Finsupp.basisSingleOne (ι := Sym (Fin 2) k) (R := ℂ)).tensorProduct
    (Finsupp.basisSingleOne (ι := Sym (Fin 2) k) (R := ℂ))

/-- The trace of an endomorphism in the displayed coefficient basis. -/
def coefficientTrace (k : ℕ)
    (f : CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k) : ℂ :=
  Matrix.trace ((LinearMap.toMatrix (coefficientMixedBasis k) (coefficientMixedBasis k)) f)

/-- The coefficient-representation character table claim. -/
def coefficientRepresentationCharacterTable_claim14726 : Prop :=
  ∀ k : ℕ,
    let n : ℂ := (k + 1 : ℕ)
    let j : ℂ := if Even k then 1 else 0
    let S := coefficientFactorSwap k
    let R_h := coefficientLeftReversal k
    let D := coefficientDoubleReversal k
    let r := S * R_h
    r ^ 2 = D ∧
    [ coefficientTrace k (1 : CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k),
      coefficientTrace k r,
      coefficientTrace k D,
      coefficientTrace k (r ^ 3),
      coefficientTrace k S,
      coefficientTrace k (D * S),
      coefficientTrace k R_h,
      coefficientTrace k (D * R_h) ] =
    [ n ^ 2, j, j ^ 2, j, n, n, n * j, n * j ]

end
end MathlibPlus.Open.RepresentationTheory
