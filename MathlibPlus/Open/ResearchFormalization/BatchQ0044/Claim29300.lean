import MathlibPlus.Open.ResearchFormalization.BatchQ0044.ScalarEigenvectors

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0044

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev ScalarAlgebra := rootedFactorAlgebra
abbrev ScalarCarrier := (ScalarAlgebra : Type)
abbrev ScalarTensor := TensorProduct ℚ ScalarCarrier ScalarCarrier
abbrev ScalarTripleTensor :=
  TensorProduct ℚ ScalarCarrier (TensorProduct ℚ ScalarCarrier ScalarCarrier)

private def operatorRestriction
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier) : Prop :=
  ∀ a : ScalarCarrier,
    (B a : RootedRing) = rootedOperator (a : RootedRing)

private noncomputable def leftCounitMap
    (ε : ScalarCarrier →ₐ[ℚ] ℚ) : ScalarTensor →ₗ[ℚ] ScalarCarrier :=
  TensorProduct.lift
    ((LinearMap.smulRightₗ (R := ℚ)
      (M := ScalarCarrier) (M₂ := ScalarCarrier)) ε.toLinearMap)

private noncomputable def rightCounitMap
    (ε : ScalarCarrier →ₐ[ℚ] ℚ) : ScalarTensor →ₗ[ℚ] ScalarCarrier :=
  (leftCounitMap ε).comp
    (TensorProduct.comm ℚ ScalarCarrier ScalarCarrier).toLinearMap

private noncomputable def coassociativeLeft
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (a : ScalarCarrier) : ScalarTripleTensor :=
  (TensorProduct.assoc ℚ ScalarCarrier ScalarCarrier ScalarCarrier)
    ((TensorProduct.map Δ.toLinearMap
      (LinearMap.id : ScalarCarrier →ₗ[ℚ] ScalarCarrier)) (Δ a))

private noncomputable def coassociativeRight
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (a : ScalarCarrier) : ScalarTripleTensor :=
  (TensorProduct.map
    (LinearMap.id : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    Δ.toLinearMap (Δ a))

private def skewAffineGraftingLaw
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    (u : ScalarCarrier) : Prop :=
  ∀ a : ScalarCarrier,
    Δ (B a) =
      (TensorProduct.tmul ℚ (B a) u) +
        TensorProduct.map
          (LinearMap.id : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
          B (Δ a)

private def counitaryCoproductLaw
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (ε : ScalarCarrier →ₐ[ℚ] ℚ) : Prop :=
  (∀ a : ScalarCarrier,
    leftCounitMap ε (Δ a) = a) ∧
    (∀ a : ScalarCarrier,
      rightCounitMap ε (Δ a) = a)

private def coassociativeCoproductLaw
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor) : Prop :=
  ∀ a : ScalarCarrier,
    coassociativeLeft Δ a = coassociativeRight Δ a

private def rootMonomialWeight (zDegree : ℕ) (m : ℕ →₀ ℕ) : ℕ :=
  zDegree + m.sum (fun i a => (i + 1) * a)

private def homogeneousRoot (P : RootedRing) (n : ℕ) : Prop :=
  ∀ z ∈ P.support, ∀ m ∈ (P.coeff z).support,
    rootMonomialWeight z m = n

private def positiveRoot (P : RootedRing) : Prop :=
  ∀ z ∈ P.support, ∀ m ∈ (P.coeff z).support,
    0 < rootMonomialWeight z m

private def higherTotalWeightSubmodule (n : ℕ) : Submodule ℚ ScalarTensor :=
  Submodule.span ℚ
    {x | ∃ p q : ScalarCarrier, ∃ i j : ℕ,
      homogeneousRoot p.1 i ∧ homogeneousRoot q.1 j ∧
        n < i + j ∧ x = TensorProduct.tmul ℚ p q}

private noncomputable def tensorNeg (x : ScalarTensor) : ScalarTensor :=
  @Neg.neg ScalarTensor
    (TensorProduct.neg (R := ℚ) (M := ScalarCarrier) (N := ScalarCarrier)) x

private def tensorSub (x y : ScalarTensor) : ScalarTensor :=
  x + tensorNeg y

private def classicalCocycleResidual
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    (a : ScalarCarrier) : ScalarTensor :=
  tensorSub (Δ (B a))
    ((TensorProduct.tmul ℚ (B a) (1 : ScalarCarrier)) +
      TensorProduct.map
        (LinearMap.id : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
        B (Δ a))

private def leastTotalWeightClassical
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    (u : ScalarCarrier) : Prop :=
  ∃ uPlus : ScalarCarrier,
    u = 1 + uPlus ∧
      positiveRoot uPlus.1 ∧
        ∀ n : ℕ, ∀ a : ScalarCarrier,
          homogeneousRoot a.1 n →
            classicalCocycleResidual Δ B a ∈
              higherTotalWeightSubmodule (n + 1)

private def scalarRelation
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    (s e p c : ScalarCarrier) : ScalarCarrier :=
  s * p - e ^ 2 - B c + B (s * e)

private def recordEightReducedResidual
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    (s e p c : ScalarCarrier) : ScalarTensor :=
  tensorSub (Δ (s * p)) (Δ (e ^ 2)) +
      TensorProduct.tmul ℚ (e ^ 2 - s * p) (1 : ScalarCarrier) +
    TensorProduct.map
      (LinearMap.id : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
      B (tensorSub (Δ (s * e)) (Δ c))

private def recordEightDefect
    (s e p c : ScalarCarrier) : ScalarTensor :=
  tensorSub (TensorProduct.tmul ℚ s (c - s * e))
      (TensorProduct.tmul ℚ (e - s ^ 2) (e - s ^ 2)) +
    TensorProduct.tmul ℚ (p - c) s

private def recordEightMiddleDefect
    (s e : ScalarCarrier) : ScalarTensor :=
  tensorNeg (TensorProduct.tmul ℚ (e - s ^ 2) (e - s ^ 2))

private def canonicalScalarData
    (s e p c : ScalarCarrier) : Prop :=
  (s : RootedRing) = scalarS ∧
    (e : RootedRing) = scalarE ∧
      (p : RootedRing) = scalarP ∧
        (c : RootedRing) = scalarC

private def recordEightObstruction
    (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier) : Prop :=
  ∃ s e p c : ScalarCarrier,
    canonicalScalarData s e p c ∧
      scalarRelation B s e p c = 0 ∧
        recordEightReducedResidual Δ B s e p c =
          recordEightDefect s e p c ∧
            recordEightMiddleDefect s e ≠ 0 ∧
              recordEightDefect s e p c ≠ 0

private def compatibleCoproductData : Prop :=
  ∃ (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
    (ε : ScalarCarrier →ₐ[ℚ] ℚ)
    (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
    (u : ScalarCarrier),
    operatorRestriction B ∧
      skewAffineGraftingLaw Δ B u ∧
        counitaryCoproductLaw Δ ε ∧
          coassociativeCoproductLaw Δ

/-- The skew-affine law has no coassociative counitary realization.  Its
counit consequence, group-like consequence, and the least-weight reduction to
the classical cocycle are stated together with the concrete Record-8 defect. -/
def claim29300_skewAffineGraftingLawsAllFail : Prop :=
  ¬ compatibleCoproductData ∧
    (∀ (Δ : ScalarCarrier →ₐ[ℚ] ScalarTensor)
      (ε : ScalarCarrier →ₐ[ℚ] ℚ)
      (B : ScalarCarrier →ₗ[ℚ] ScalarCarrier)
      (u : ScalarCarrier),
      operatorRestriction B →
        skewAffineGraftingLaw Δ B u →
          counitaryCoproductLaw Δ ε →
            (∀ a : ScalarCarrier, ε (B a) = 0) ∧
              (coassociativeCoproductLaw Δ →
                Δ u = TensorProduct.tmul ℚ u u ∧
                  ε u = 1 ∧
                    leastTotalWeightClassical Δ B u ∧
                      recordEightObstruction Δ B))

end
end MathlibPlus.Open.ResearchFormalization.BatchQ0044
