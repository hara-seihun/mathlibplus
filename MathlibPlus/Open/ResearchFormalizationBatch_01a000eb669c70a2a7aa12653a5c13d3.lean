import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000eb669c70a2a7aa12653a5c13d3

noncomputable section

/-- The planar free magma on the two generators from Claim 27617. -/
inductive PlanarMagma
  | a
  | b
  | node (left right : PlanarMagma)
  deriving DecidableEq

namespace PlanarMagma

def wt : PlanarMagma → Nat
  | .a => 1
  | .b => 2
  | .node x y => 1 + wt x + wt y

end PlanarMagma

abbrev F := PlanarMagma →₀ ℚ

def basis (x : PlanarMagma) : F := Finsupp.single x 1

def linearExtend {α N : Type*} [AddCommMonoid N] [Module ℚ N]
    (v : α → N) : (α →₀ ℚ) →ₗ[ℚ] N :=
  Finsupp.lsum ℚ (fun x => LinearMap.smulRight (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (v x))

def magmaMul : F →ₗ[ℚ] F →ₗ[ℚ] F :=
  linearExtend (fun x => linearExtend (fun y => basis (.node x y)))

def planarDerivationOnBasis (t : PlanarMagma) : F :=
  match t with
  | .a => basis .b
  | .b => 2 • basis (.node .a .a)
  | .node x y => magmaMul (planarDerivationOnBasis x) (basis y) +
      magmaMul (basis x) (planarDerivationOnBasis y)
  termination_by structural t

def planarDerivation : F →ₗ[ℚ] F := linearExtend planarDerivationOnBasis

/-- Claim 27617: the Leibniz derivation on the displayed planar free magma is injective. -/
def planarFreeMagmaInjectiveDerivation : Prop :=
  Function.Injective planarDerivation

abbrev H := TensorProduct ℚ F F

def tensorD : H →ₗ[ℚ] H :=
  TensorProduct.map planarDerivation (LinearMap.id : F →ₗ[ℚ] F) +
    TensorProduct.map (LinearMap.id : F →ₗ[ℚ] F) planarDerivation

def tensorECoefficient (x : PlanarMagma) : F →ₗ[ℚ] H :=
  2 • ((TensorProduct.mk ℚ F F) (basis .a)).comp (magmaMul (basis x)) +
    2 • ((LinearMap.flip (TensorProduct.mk ℚ F F)) (basis .a)).comp
      (magmaMul (basis x))

def tensorEBilinear : F →ₗ[ℚ] (F →ₗ[ℚ] H) := linearExtend tensorECoefficient

def tensorE : H →ₗ[ℚ] H := TensorProduct.lift tensorEBilinear

/-- Claim 27621: the tensor derivation and root-forgetting correction have the displayed formulas. -/
def tensorDerivationAndRootForgettingCorrection : Prop :=
  (∀ x y : F, tensorD (TensorProduct.tmul ℚ x y) =
      TensorProduct.tmul ℚ (planarDerivation x) y +
        TensorProduct.tmul ℚ x (planarDerivation y)) ∧
  (∀ x y : F, tensorE (TensorProduct.tmul ℚ x y) =
      2 • (TensorProduct.tmul ℚ (basis .a) (magmaMul x y) +
        TensorProduct.tmul ℚ (magmaMul x y) (basis .a)))

def pointedGrowth : (H × H) →ₗ[ℚ] (H × H) :=
  (tensorD.comp (LinearMap.fst ℚ H H) + tensorE.comp (LinearMap.snd ℚ H H)).prod
    ((LinearMap.fst ℚ H H) + tensorD.comp (LinearMap.snd ℚ H H))

/-- Claim 27622: the pointed growth operator has the stated root-color formulas and block matrix. -/
def exactPointedGrowthOperator : Prop :=
  (∀ x y : F,
    pointedGrowth (TensorProduct.tmul ℚ x y, 0) =
      (tensorD (TensorProduct.tmul ℚ x y), TensorProduct.tmul ℚ x y)) ∧
  (∀ x y : F,
    pointedGrowth (0, TensorProduct.tmul ℚ x y) =
      (tensorE (TensorProduct.tmul ℚ x y), tensorD (TensorProduct.tmul ℚ x y)))

/-- Claim 27628: the Schur operator has zero kernel, equivalently is injective. -/
def injectivityOfSchurOperator : Prop :=
  Function.Injective (tensorE - tensorD.comp tensorD)

end

end MathlibPlus.Open.ResearchFormalizationBatch_01a000eb669c70a2a7aa12653a5c13d3
