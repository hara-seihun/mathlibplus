import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

open scoped TensorProduct

namespace MathlibPlus.Open.ResearchFormalization.R0666Claim29477

open MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev AF := (scalarRootedFactorAlgebra : Type)
abbrev AmbientTensor := TensorProduct ℚ RootRing RootRing

def eCoordinate (k : ℕ) : RootRing :=
  triangularDifference k

def ambientS : AmbientTensor :=
  scalarS ⊗ₜ[ℚ] (1 : RootRing) + (1 : RootRing) ⊗ₜ[ℚ] scalarS

def ambientZ : AmbientTensor :=
  rootZ ⊗ₜ[ℚ] (1 : RootRing) + (1 : RootRing) ⊗ₜ[ℚ] rootZ

def ambientE (k : ℕ) : AmbientTensor :=
  eCoordinate k ⊗ₜ[ℚ] eCoordinate k

def ambientX (i : ℕ) : AmbientTensor :=
  if i = 0 then ambientS - ambientZ
  else ambientE (i + 1) + ambientZ ^ i * (ambientS - ambientZ)

def ambientCoefficientMap : CoefficientRing →ₐ[ℚ] AmbientTensor :=
  MvPolynomial.aeval ambientX

def ambientCoproduct : RootRing →ₐ[ℚ] AmbientTensor :=
  Polynomial.eval₂AlgHom ambientCoefficientMap ambientZ
    (fun x => mul_comm (ambientCoefficientMap x) ambientZ)

def ambientCounitCoefficientMap : CoefficientRing →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval (fun i => if i = 0 then 0 else 1)

def ambientCounit : RootRing →ₐ[ℚ] ℚ :=
  Polynomial.eval₂AlgHom ambientCounitCoefficientMap 0
    (fun x => mul_comm (ambientCounitCoefficientMap x) 0)

def ambientAssignments : Prop :=
  ambientCoproduct scalarS = ambientS ∧
    ambientCoproduct rootZ = ambientZ ∧
    (∀ k : triangularIndex,
      ambientCoproduct (eCoordinate k.1) = ambientE k.1) ∧
    ambientCounit scalarS = 0 ∧
    ambientCounit rootZ = 0 ∧
    (∀ k : triangularIndex, ambientCounit (eCoordinate k.1) = 1)

def afTensorInclusion :
    TensorProduct ℚ AF AF →ₗ[ℚ] AmbientTensor :=
  TensorProduct.map scalarRootedFactorAlgebra.val.toLinearMap
    scalarRootedFactorAlgebra.val.toLinearMap

abbrev AFCoproduct := AF →ₐ[ℚ] TensorProduct ℚ AF AF
abbrev AFCounit := AF →ₐ[ℚ] ℚ

def residualBialgebra (Δ : AFCoproduct) (ε : AFCounit) : Prop :=
  (∀ a : AF,
    TensorProduct.assoc ℚ AF AF AF
        (Δ.toLinearMap.rTensor AF (Δ.toLinearMap a)) =
      Δ.toLinearMap.lTensor AF (Δ.toLinearMap a)) ∧
    (∀ a : AF,
      ε.toLinearMap.rTensor AF (Δ.toLinearMap a) =
        (1 : ℚ) ⊗ₜ[ℚ] a) ∧
    (∀ a : AF,
      ε.toLinearMap.lTensor AF (Δ.toLinearMap a) =
        a ⊗ₜ[ℚ] (1 : ℚ)) ∧
    (∀ a : AF,
      (TensorProduct.comm ℚ AF AF) (Δ a) = Δ a)

def ambientRestriction (Δ : AFCoproduct) (ε : AFCounit) : Prop :=
  (∀ a : AF, afTensorInclusion (Δ a) = ambientCoproduct a.1) ∧
    (∀ a : AF, ε a = ambientCounit a.1)

def afUnitMap : ℚˣ →* AFˣ :=
  Units.map (algebraMap ℚ AF)

def afUnitsAreRational : Prop :=
  Function.Surjective afUnitMap

def afNonconstant (e : AF) : Prop :=
  ¬ ∃ q : ℚ, e = algebraMap ℚ AF q

def claim29477 : Prop :=
  ambientAssignments ∧
    afUnitsAreRational ∧
      ∃ (Δ : AFCoproduct) (ε : AFCounit),
        residualBialgebra Δ ε ∧
          ambientRestriction Δ ε ∧
            ∀ k : triangularIndex,
              ∃ e : AF,
                e.1 = eCoordinate k.1 ∧
                  Δ e = e ⊗ₜ[ℚ] e ∧
                    ε e = 1 ∧ afNonconstant e ∧ ¬ IsUnit e

end

end MathlibPlus.Open.ResearchFormalization.R0666Claim29477
