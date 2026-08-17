import Mathlib
import MathlibPlus.Open.Combinatorics.AdmittedPointedGraphCarrier

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

private structure InducedGraphHopfFiniteGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

private def inducedGraphHopfGraphIso
    (G H : InducedGraphHopfFiniteGraph) : Prop :=
  ∃ e : Fin G.n ≃ Fin H.n,
    ∀ u v, G.graph.Adj u v ↔ H.graph.Adj (e u) (e v)

private abbrev InducedGraphHopfGraphClass := Quot inducedGraphHopfGraphIso
private abbrev InducedGraphHopfGraphSpace := InducedGraphHopfGraphClass →₀ ℚ
private abbrev InducedGraphHopfPointedClass := Quot PointedGraphIso
private abbrev InducedGraphHopfPointedSpace :=
  pointedGraphSpace InducedGraphHopfPointedClass

private abbrev InducedGraphHopfGraphTensorSpace :=
  TensorProduct ℚ InducedGraphHopfGraphSpace InducedGraphHopfGraphSpace
private abbrev InducedGraphHopfPointedTensorSpace :=
  TensorProduct ℚ InducedGraphHopfPointedSpace InducedGraphHopfGraphSpace

private def inducedGraphHopfGraphBasis
    (G : InducedGraphHopfFiniteGraph) : InducedGraphHopfGraphSpace :=
  Finsupp.single (Quot.mk inducedGraphHopfGraphIso G) (1 : ℚ)

private def inducedGraphHopfPointedBasis
    (G : PointedFiniteSimpleGraph) : InducedGraphHopfPointedSpace :=
  Finsupp.single (Quot.mk PointedGraphIso G) (1 : ℚ)

private def inducedGraphHopfEmptyGraph : InducedGraphHopfFiniteGraph :=
  { n := 0, graph := ⊥ }

private def inducedGraphHopfGraphUnit : InducedGraphHopfGraphSpace :=
  inducedGraphHopfGraphBasis inducedGraphHopfEmptyGraph

private def inducedGraphHopfDisjointUnion
    (G H : InducedGraphHopfFiniteGraph) : InducedGraphHopfFiniteGraph :=
  { n := G.n + H.n
    graph := (G.graph.sum H.graph).comap
      (finSumFinEquiv (m := G.n) (n := H.n)).symm }

private def inducedGraphHopfPointedDisjointUnion
    (G : PointedFiniteSimpleGraph)
    (H : InducedGraphHopfFiniteGraph) : PointedFiniteSimpleGraph :=
  { n := G.n + H.n
    graph := (G.graph.sum H.graph).comap
      (finSumFinEquiv (m := G.n) (n := H.n)).symm
    root := (finSumFinEquiv (m := G.n) (n := H.n)) (.inl G.root) }

private def inducedGraphHopfInduced
    (G : InducedGraphHopfFiniteGraph)
    (S : Finset (Fin G.n)) : InducedGraphHopfFiniteGraph :=
  { n := S.card
    graph := (G.graph.induce (S : Set (Fin G.n))).comap S.equivFin.symm }

private def inducedGraphHopfPointedInduced
    (G : PointedFiniteSimpleGraph)
    (S : Finset (Fin G.n)) (hr : G.root ∈ S) : PointedFiniteSimpleGraph :=
  { n := S.card
    graph := (G.graph.induce (S : Set (Fin G.n))).comap S.equivFin.symm
    root := S.equivFin ⟨G.root, hr⟩ }

private def inducedGraphHopfPointedDelete
    (G : PointedFiniteSimpleGraph)
    (S : Finset (Fin G.n)) (hr : G.root ∉ S) : PointedFiniteSimpleGraph :=
  inducedGraphHopfPointedInduced G Sᶜ (Finset.mem_compl.mpr hr)

private def inducedGraphHopfProductTensor
    (product : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfGraphSpace) :
    InducedGraphHopfGraphTensorSpace →ₗ[ℚ] InducedGraphHopfGraphSpace :=
  TensorProduct.lift product

private def inducedGraphHopfActionTensor
    (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace) :
    InducedGraphHopfPointedTensorSpace →ₗ[ℚ]
      InducedGraphHopfPointedSpace :=
  TensorProduct.lift action

private def inducedGraphHopfCanonicalProjector
    (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace)
    (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedTensorSpace)
    (antipode : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace) :
    InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedSpace :=
  (inducedGraphHopfActionTensor action).comp
    ((TensorProduct.map LinearMap.id antipode).comp coaction)

private def inducedGraphHopfReconstruction
    (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace)
    (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedTensorSpace)
    (projector : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedSpace) :
    InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedSpace :=
  (inducedGraphHopfActionTensor action).comp
    ((TensorProduct.map projector LinearMap.id).comp coaction)

private def inducedGraphHopfConvolution
    (product : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfGraphSpace)
    (coproduct : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphTensorSpace)
    (f g : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace) :
    InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace :=
  (inducedGraphHopfProductTensor product).comp
    ((TensorProduct.map f g).comp coproduct)

section ExactGraphHopfSystem

variable
  (product : InducedGraphHopfGraphSpace →ₗ[ℚ]
    InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfGraphSpace)
  (tensorProductProduct :
    TensorProduct ℚ InducedGraphHopfGraphTensorSpace
      InducedGraphHopfGraphTensorSpace →ₗ[ℚ]
        InducedGraphHopfGraphTensorSpace)
  (coproduct : InducedGraphHopfGraphSpace →ₗ[ℚ]
    InducedGraphHopfGraphTensorSpace)
  (counit : InducedGraphHopfGraphSpace →ₗ[ℚ] ℚ)
  (antipode : InducedGraphHopfGraphSpace →ₗ[ℚ]
    InducedGraphHopfGraphSpace)
  (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
    InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace)
  (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
    InducedGraphHopfPointedTensorSpace)
  (graphCounitLeft graphCounitRight :
    InducedGraphHopfGraphTensorSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace)
  (pointedCounit : InducedGraphHopfPointedTensorSpace →ₗ[ℚ]
    InducedGraphHopfPointedSpace)
  (middleSwap :
    TensorProduct ℚ
        (TensorProduct ℚ InducedGraphHopfPointedSpace
          InducedGraphHopfGraphSpace)
        (TensorProduct ℚ InducedGraphHopfGraphSpace
          InducedGraphHopfGraphSpace) →ₗ[ℚ]
      TensorProduct ℚ
        (TensorProduct ℚ InducedGraphHopfPointedSpace
          InducedGraphHopfGraphSpace)
        (TensorProduct ℚ InducedGraphHopfGraphSpace
          InducedGraphHopfGraphSpace))
  (K : Submodule ℚ InducedGraphHopfPointedSpace)
  (projector : InducedGraphHopfPointedSpace →ₗ[ℚ] K)

include product tensorProductProduct coproduct counit antipode action coaction
  graphCounitLeft graphCounitRight pointedCounit middleSwap K projector

private def inducedGraphHopfSemantics : Prop :=
  (∀ G H : InducedGraphHopfFiniteGraph,
    product (inducedGraphHopfGraphBasis G)
      (inducedGraphHopfGraphBasis H) =
      inducedGraphHopfGraphBasis (inducedGraphHopfDisjointUnion G H)) ∧
  (∀ G : InducedGraphHopfFiniteGraph,
    coproduct (inducedGraphHopfGraphBasis G) =
      ∑ S : Finset (Fin G.n),
        TensorProduct.tmul ℚ
          (inducedGraphHopfGraphBasis
            (inducedGraphHopfInduced G Sᶜ))
          (inducedGraphHopfGraphBasis
            (inducedGraphHopfInduced G S))) ∧
  (∀ G : PointedFiniteSimpleGraph,
    ∀ H : InducedGraphHopfFiniteGraph,
      action (inducedGraphHopfPointedBasis G)
        (inducedGraphHopfGraphBasis H) =
        inducedGraphHopfPointedBasis
          (inducedGraphHopfPointedDisjointUnion G H)) ∧
  (∀ G : PointedFiniteSimpleGraph,
    coaction (inducedGraphHopfPointedBasis G) =
      ∑ S : {S : Finset (Fin G.n) // G.root ∉ S},
        TensorProduct.tmul ℚ
          (inducedGraphHopfPointedBasis
            (inducedGraphHopfPointedDelete G S.1 S.2))
          (inducedGraphHopfGraphBasis
            (inducedGraphHopfInduced
              { n := G.n, graph := G.graph } S.1))) ∧
  (∀ G : InducedGraphHopfFiniteGraph,
    counit (inducedGraphHopfGraphBasis G) =
      if G.n = 0 then 1 else 0) ∧
  (∀ x y z w : InducedGraphHopfGraphSpace,
    tensorProductProduct
        (TensorProduct.tmul ℚ
          (TensorProduct.tmul ℚ x y)
          (TensorProduct.tmul ℚ z w)) =
      TensorProduct.tmul ℚ (product x z) (product y w)) ∧
  coproduct.comp (inducedGraphHopfProductTensor product) =
    tensorProductProduct.comp
      (TensorProduct.map coproduct coproduct) ∧
  (∀ x y : InducedGraphHopfGraphSpace,
    counit (product x y) = counit x * counit y) ∧
  counit inducedGraphHopfGraphUnit = 1 ∧
  (∀ x y z : InducedGraphHopfGraphSpace,
    product (product x y) z = product x (product y z)) ∧
  (∀ x y : InducedGraphHopfGraphSpace,
    product x y = product y x) ∧
  (∀ x : InducedGraphHopfGraphSpace,
    product x inducedGraphHopfGraphUnit = x ∧
      product inducedGraphHopfGraphUnit x = x) ∧
  (∀ x : InducedGraphHopfGraphSpace,
    (inducedGraphHopfConvolution product coproduct antipode
        LinearMap.id) x = counit x • inducedGraphHopfGraphUnit) ∧
  (∀ x : InducedGraphHopfGraphSpace,
    (inducedGraphHopfConvolution product coproduct LinearMap.id
        antipode) x = counit x • inducedGraphHopfGraphUnit) ∧
  (TensorProduct.assoc ℚ InducedGraphHopfGraphSpace
      InducedGraphHopfGraphSpace InducedGraphHopfGraphSpace).symm.toLinearMap.comp
      ((TensorProduct.map LinearMap.id coproduct).comp coproduct) =
    (TensorProduct.map coproduct LinearMap.id).comp coproduct ∧
  (∀ x y : InducedGraphHopfGraphSpace,
    graphCounitLeft (TensorProduct.tmul ℚ x y) = counit x • y) ∧
  (∀ x y : InducedGraphHopfGraphSpace,
    graphCounitRight (TensorProduct.tmul ℚ x y) = counit y • x) ∧
  graphCounitLeft.comp coproduct = LinearMap.id ∧
  graphCounitRight.comp coproduct = LinearMap.id ∧
  (∀ (m : InducedGraphHopfPointedSpace)
      (h₁ h₂ : InducedGraphHopfGraphSpace),
    action (action m h₁) h₂ = action m (product h₁ h₂)) ∧
  (∀ m : InducedGraphHopfPointedSpace,
    action m inducedGraphHopfGraphUnit = m) ∧
  (TensorProduct.assoc ℚ InducedGraphHopfPointedSpace
      InducedGraphHopfGraphSpace InducedGraphHopfGraphSpace).symm.toLinearMap.comp
      ((TensorProduct.map LinearMap.id coproduct).comp coaction) =
    (TensorProduct.map coaction LinearMap.id).comp coaction ∧
  (∀ (m : InducedGraphHopfPointedSpace)
      (h : InducedGraphHopfGraphSpace),
    pointedCounit (TensorProduct.tmul ℚ m h) = counit h • m) ∧
  pointedCounit.comp coaction = LinearMap.id ∧
  (∀ m h₁ h₂ h₃,
    middleSwap
      (TensorProduct.tmul ℚ
        (TensorProduct.tmul ℚ m h₁)
        (TensorProduct.tmul ℚ h₂ h₃)) =
      TensorProduct.tmul ℚ
        (TensorProduct.tmul ℚ m h₂)
        (TensorProduct.tmul ℚ h₁ h₃)) ∧
  coaction.comp (inducedGraphHopfActionTensor action) =
    (TensorProduct.map (inducedGraphHopfActionTensor action)
        (inducedGraphHopfProductTensor product)).comp
      (middleSwap.comp
        (TensorProduct.map coaction coproduct)) ∧
  (∀ m : InducedGraphHopfPointedSpace,
    m ∈ K ↔
      coaction m =
        TensorProduct.tmul ℚ m inducedGraphHopfGraphUnit) ∧
  (∀ m : InducedGraphHopfPointedSpace,
    K.subtype (projector m) =
      inducedGraphHopfCanonicalProjector action coaction antipode m) ∧
  (∀ (m : InducedGraphHopfPointedSpace)
      (h : InducedGraphHopfGraphSpace),
    projector (action m h) = counit h • projector m)

end ExactGraphHopfSystem

section RightModuleAndComodule

variable {N : Type*} [AddCommGroup N] [Module ℚ N]

private def inducedGraphHopfActionTensorN
    (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N) :
    TensorProduct ℚ N InducedGraphHopfGraphSpace →ₗ[ℚ] N :=
  TensorProduct.lift actionN

private def inducedGraphHopfRightModuleAxioms
    (product : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfGraphSpace)
    (unit : InducedGraphHopfGraphSpace)
    (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N) : Prop :=
  (∀ (n : N) (h₁ h₂ : InducedGraphHopfGraphSpace),
    actionN (actionN n h₁) h₂ = actionN n (product h₁ h₂)) ∧
  (∀ n : N, actionN n unit = n)

private def inducedGraphHopfRightModuleHom
    (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace)
    (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N)
    (f : InducedGraphHopfPointedSpace →ₗ[ℚ] N) : Prop :=
  ∀ m h, f (action m h) = actionN (f m) h

private def inducedGraphHopfRightComoduleAxioms
    (coproduct : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphTensorSpace)
    (counit : InducedGraphHopfGraphSpace →ₗ[ℚ] ℚ)
    (rho : N →ₗ[ℚ]
      TensorProduct ℚ N InducedGraphHopfGraphSpace)
    (counitTensor : TensorProduct ℚ N InducedGraphHopfGraphSpace →ₗ[ℚ] N) : Prop :=
  (TensorProduct.assoc ℚ N InducedGraphHopfGraphSpace
      InducedGraphHopfGraphSpace).symm.toLinearMap.comp
      ((TensorProduct.map LinearMap.id coproduct).comp rho) =
    (TensorProduct.map rho LinearMap.id).comp rho ∧
  (∀ n h, counitTensor (TensorProduct.tmul ℚ n h) = counit h • n) ∧
  counitTensor.comp rho = LinearMap.id

private def inducedGraphHopfComoduleHom
    (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedTensorSpace)
    (rho : N →ₗ[ℚ]
      TensorProduct ℚ N InducedGraphHopfGraphSpace)
    (f : N →ₗ[ℚ] InducedGraphHopfPointedSpace) : Prop :=
  (TensorProduct.map f LinearMap.id).comp rho = coaction.comp f

private def inducedGraphHopfComoduleHomOut
    (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedTensorSpace)
    (rho : N →ₗ[ℚ]
      TensorProduct ℚ N InducedGraphHopfGraphSpace)
    (f : InducedGraphHopfPointedSpace →ₗ[ℚ] N) : Prop :=
  (TensorProduct.map f LinearMap.id).comp coaction = rho.comp f

private def inducedGraphHopfRightHopfModuleAxioms
    (product : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfGraphSpace)
    (unit : InducedGraphHopfGraphSpace)
    (coproduct : InducedGraphHopfGraphSpace →ₗ[ℚ]
      InducedGraphHopfGraphTensorSpace)
    (counit : InducedGraphHopfGraphSpace →ₗ[ℚ] ℚ)
    (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N)
    (rho : N →ₗ[ℚ]
      TensorProduct ℚ N InducedGraphHopfGraphSpace)
    (counitTensor : TensorProduct ℚ N InducedGraphHopfGraphSpace →ₗ[ℚ] N)
    (middleSwapN :
      TensorProduct ℚ
          (TensorProduct ℚ N InducedGraphHopfGraphSpace)
          (TensorProduct ℚ InducedGraphHopfGraphSpace
            InducedGraphHopfGraphSpace) →ₗ[ℚ]
        TensorProduct ℚ
          (TensorProduct ℚ N InducedGraphHopfGraphSpace)
          (TensorProduct ℚ InducedGraphHopfGraphSpace
            InducedGraphHopfGraphSpace)) : Prop :=
  inducedGraphHopfRightModuleAxioms product unit actionN ∧
  inducedGraphHopfRightComoduleAxioms coproduct counit rho counitTensor ∧
  (∀ (n : N) (h₁ h₂ h₃ : InducedGraphHopfGraphSpace),
    middleSwapN
      (TensorProduct.tmul ℚ
        (TensorProduct.tmul ℚ n h₁)
        (TensorProduct.tmul ℚ h₂ h₃)) =
      TensorProduct.tmul ℚ
        (TensorProduct.tmul ℚ n h₂)
        (TensorProduct.tmul ℚ h₁ h₃)) ∧
  rho.comp (inducedGraphHopfActionTensorN actionN) =
    (TensorProduct.map (inducedGraphHopfActionTensorN actionN)
        (inducedGraphHopfProductTensor product)).comp
      (middleSwapN.comp (TensorProduct.map rho coproduct))

private def inducedGraphHopfHopfModuleHom
    (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace)
    (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
      InducedGraphHopfPointedTensorSpace)
    (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N)
    (rho : N →ₗ[ℚ]
      TensorProduct ℚ N InducedGraphHopfGraphSpace)
    (f : InducedGraphHopfPointedSpace →ₗ[ℚ] N) : Prop :=
  inducedGraphHopfRightModuleHom action actionN f ∧
  inducedGraphHopfComoduleHomOut coaction rho f

private def inducedGraphHopfCoinvariants
    (unit : InducedGraphHopfGraphSpace)
    (rho : N →ₗ[ℚ]
      TensorProduct ℚ N InducedGraphHopfGraphSpace)
    (KN : Submodule ℚ N) : Prop :=
  ∀ n : N, n ∈ KN ↔ rho n = TensorProduct.tmul ℚ n unit

end RightModuleAndComodule

section Claims

variable
  (product : InducedGraphHopfGraphSpace →ₗ[ℚ]
    InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfGraphSpace)
  (tensorProductProduct :
    TensorProduct ℚ InducedGraphHopfGraphTensorSpace
      InducedGraphHopfGraphTensorSpace →ₗ[ℚ]
        InducedGraphHopfGraphTensorSpace)
  (coproduct : InducedGraphHopfGraphSpace →ₗ[ℚ]
    InducedGraphHopfGraphTensorSpace)
  (counit : InducedGraphHopfGraphSpace →ₗ[ℚ] ℚ)
  (antipode : InducedGraphHopfGraphSpace →ₗ[ℚ]
    InducedGraphHopfGraphSpace)
  (action : InducedGraphHopfPointedSpace →ₗ[ℚ]
    InducedGraphHopfGraphSpace →ₗ[ℚ] InducedGraphHopfPointedSpace)
  (coaction : InducedGraphHopfPointedSpace →ₗ[ℚ]
    InducedGraphHopfPointedTensorSpace)
  (graphCounitLeft graphCounitRight :
    InducedGraphHopfGraphTensorSpace →ₗ[ℚ]
      InducedGraphHopfGraphSpace)
  (pointedCounit : InducedGraphHopfPointedTensorSpace →ₗ[ℚ]
    InducedGraphHopfPointedSpace)
  (middleSwap :
    TensorProduct ℚ
        (TensorProduct ℚ InducedGraphHopfPointedSpace
          InducedGraphHopfGraphSpace)
        (TensorProduct ℚ InducedGraphHopfGraphSpace
          InducedGraphHopfGraphSpace) →ₗ[ℚ]
      TensorProduct ℚ
        (TensorProduct ℚ InducedGraphHopfPointedSpace
          InducedGraphHopfGraphSpace)
        (TensorProduct ℚ InducedGraphHopfGraphSpace
          InducedGraphHopfGraphSpace))
  (K : Submodule ℚ InducedGraphHopfPointedSpace)
  (projector : InducedGraphHopfPointedSpace →ₗ[ℚ] K)

def claim22987 : Prop :=
  inducedGraphHopfSemantics product tensorProductProduct coproduct counit antipode action coaction
      graphCounitLeft graphCounitRight pointedCounit middleSwap K projector →
    ∀ m : InducedGraphHopfPointedSpace,
      m = inducedGraphHopfReconstruction action coaction
        (K.subtype.comp projector) m

def claim22988 : Prop :=
  inducedGraphHopfSemantics product tensorProductProduct coproduct counit antipode action coaction
      graphCounitLeft graphCounitRight pointedCounit middleSwap K projector →
    ∀ {N : Type*} [AddCommGroup N] [Module ℚ N]
      (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N),
      inducedGraphHopfRightModuleAxioms product inducedGraphHopfGraphUnit
        actionN →
      ∃ e :
          {f : InducedGraphHopfPointedSpace →ₗ[ℚ] N //
            inducedGraphHopfRightModuleHom action actionN f} ≃
            (K →ₗ[ℚ] N),
        (∀ f, e f = f.1.comp K.subtype) ∧
        (∀ (g : K →ₗ[ℚ] N) (k : K)
            (h : InducedGraphHopfGraphSpace),
          (e.symm g).1 (action (K.subtype k) h) =
            actionN (g k) h)

def claim22989 : Prop :=
  inducedGraphHopfSemantics product tensorProductProduct coproduct counit antipode action coaction
      graphCounitLeft graphCounitRight pointedCounit middleSwap K projector →
    (∃ e :
        (TensorProduct ℚ K InducedGraphHopfGraphSpace) ≃ₗ[ℚ]
          InducedGraphHopfPointedSpace,
        e.toLinearMap =
            (inducedGraphHopfActionTensor action).comp
              (TensorProduct.map K.subtype LinearMap.id) ∧
        e.symm.toLinearMap =
            (TensorProduct.map projector LinearMap.id).comp coaction) ∧
    ∀ {N : Type*} [AddCommGroup N] [Module ℚ N]
      (rho : N →ₗ[ℚ]
        TensorProduct ℚ N InducedGraphHopfGraphSpace)
      (counitTensor : TensorProduct ℚ N InducedGraphHopfGraphSpace →ₗ[ℚ] N),
      inducedGraphHopfRightComoduleAxioms coproduct counit rho counitTensor →
      ∀ (g : N →ₗ[ℚ] K),
        ∃! f : N →ₗ[ℚ] InducedGraphHopfPointedSpace,
          inducedGraphHopfComoduleHom coaction rho f ∧
          projector.comp f = g ∧
          f = (inducedGraphHopfActionTensor action).comp
            ((TensorProduct.map (K.subtype.comp g) LinearMap.id).comp rho)

def claim22990 : Prop :=
  inducedGraphHopfSemantics product tensorProductProduct coproduct counit antipode action coaction
      graphCounitLeft graphCounitRight pointedCounit middleSwap K projector →
    ∀ {N : Type*} [AddCommGroup N] [Module ℚ N]
      (actionN : N →ₗ[ℚ] InducedGraphHopfGraphSpace →ₗ[ℚ] N)
      (rho : N →ₗ[ℚ]
        TensorProduct ℚ N InducedGraphHopfGraphSpace)
      (counitTensor : TensorProduct ℚ N InducedGraphHopfGraphSpace →ₗ[ℚ] N)
      (middleSwapN :
        TensorProduct ℚ
            (TensorProduct ℚ N InducedGraphHopfGraphSpace)
            (TensorProduct ℚ InducedGraphHopfGraphSpace
              InducedGraphHopfGraphSpace) →ₗ[ℚ]
          TensorProduct ℚ
            (TensorProduct ℚ N InducedGraphHopfGraphSpace)
            (TensorProduct ℚ InducedGraphHopfGraphSpace
              InducedGraphHopfGraphSpace)),
      inducedGraphHopfRightHopfModuleAxioms
        product inducedGraphHopfGraphUnit coproduct counit actionN rho
          counitTensor middleSwapN →
      ∀ (KN : Submodule ℚ N),
        inducedGraphHopfCoinvariants inducedGraphHopfGraphUnit rho KN →
        (∃ e :
            {f : InducedGraphHopfPointedSpace →ₗ[ℚ] N //
              inducedGraphHopfHopfModuleHom action coaction actionN rho f} ≃
              (K →ₗ[ℚ] KN),
          (∀ f k,
            KN.subtype ((e f) k) = f.1 (K.subtype k)) ∧
          (∀ (g : K →ₗ[ℚ] KN) (k : K)
              (h : InducedGraphHopfGraphSpace),
            (e.symm g).1 (action (K.subtype k) h) =
              actionN (KN.subtype (g k)) h)) ∧
        (∃ eN :
            (TensorProduct ℚ KN InducedGraphHopfGraphSpace) ≃ₗ[ℚ] N,
          eN.toLinearMap =
            (inducedGraphHopfActionTensorN actionN).comp
              (TensorProduct.map KN.subtype LinearMap.id) ∧
          rho.comp eN.toLinearMap =
            (TensorProduct.map eN.toLinearMap LinearMap.id).comp
              ((TensorProduct.assoc ℚ KN InducedGraphHopfGraphSpace
                  InducedGraphHopfGraphSpace).symm.toLinearMap.comp
                (TensorProduct.map LinearMap.id coproduct)))

end Claims

end

end MathlibPlus.Open.ResearchFormalizationBatch
