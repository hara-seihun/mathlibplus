import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1534.BinarySizeEight

noncomputable section

abbrev BinaryField := ZMod 2
abbrev BinaryModule := Fin 3 → BinaryField
abbrev TernarySquareGroup := Multiplicative (ZMod 3 × ZMod 3)
abbrev BinaryGeneralLinear := BinaryModule ≃ₗ[BinaryField] BinaryModule

abbrev BinaryRepresentation :=
  {ρ : TernarySquareGroup → BinaryGeneralLinear //
    ρ 1 = 1 ∧ ∀ x y : TernarySquareGroup, ρ (x * y) = ρ x * ρ y}

def binaryInvariantSubmodule (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W : Submodule BinaryField BinaryModule) : Prop :=
  ∀ h : TernarySquareGroup,
    Submodule.map (ρ h).toLinearMap W = W

def binarySemisimpleRepresentation (ρ : TernarySquareGroup → BinaryGeneralLinear) : Prop :=
  ∀ W : Submodule BinaryField BinaryModule,
    binaryInvariantSubmodule ρ W →
      ∃ U : Submodule BinaryField BinaryModule,
        binaryInvariantSubmodule ρ U ∧ IsCompl W U

def binarySimpleModuleRepresentation {M : Type*} [AddCommGroup M]
    [Module BinaryField M] [FiniteDimensional BinaryField M]
    (ρ : TernarySquareGroup → (M ≃ₗ[BinaryField] M)) : Prop :=
  ρ 1 = 1 ∧
    (∀ x y : TernarySquareGroup, ρ (x * y) = ρ x * ρ y) ∧
    Nontrivial M ∧
      ∀ W : Submodule BinaryField M,
        (∀ h : TernarySquareGroup,
          Submodule.map (ρ h).toLinearMap W = W) →
        W = ⊥ ∨ W = ⊤

def binaryCubicFactorization : Prop :=
  (Polynomial.X ^ 3 - 1 : Polynomial BinaryField) =
    (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1)

def binarySourceOrbitBlock (W : Submodule BinaryField BinaryModule)
    (v : BinaryModule) (h : TernarySquareGroup) : Set (BinaryModule × TernarySquareGroup) :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (w : BinaryModule)}

def binaryPulledBackTargetOrbitBlock
    (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W : Submodule BinaryField BinaryModule) (v : BinaryModule)
    (h : TernarySquareGroup) : Set (BinaryModule × TernarySquareGroup) :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (ρ h).symm (w : BinaryModule)}

def binaryPureFiberRelation :
    (BinaryModule × TernarySquareGroup) →
      (BinaryModule × TernarySquareGroup) → Prop :=
  fun p q => p.2 = q.2

def binaryWCosetRelation (W : Submodule BinaryField BinaryModule) :
    (BinaryModule × TernarySquareGroup) →
      (BinaryModule × TernarySquareGroup) → Prop :=
  fun p q =>
    p.2 = q.2 ∧ ∃ w₁ w₂ : W,
      p.1 + (w₁ : BinaryModule) = q.1 + (w₂ : BinaryModule)

def binaryCommonBlockCard (W : Submodule BinaryField BinaryModule)
    (v : BinaryModule) (h : TernarySquareGroup) : ℕ :=
  Nat.card {p : BinaryModule × TernarySquareGroup //
    p ∈ binarySourceOrbitBlock W v h}

def binaryStrictCommonRefinement
    (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W : Submodule BinaryField BinaryModule) : Prop :=
  W ≠ ⊥ ∧ W ≠ ⊤ ∧
    binaryInvariantSubmodule ρ W ∧
    (∀ v : BinaryModule, ∀ h : TernarySquareGroup,
      binarySourceOrbitBlock W v h = binaryPulledBackTargetOrbitBlock ρ W v h) ∧
    (∀ p q : BinaryModule × TernarySquareGroup,
      binaryWCosetRelation W p q → binaryPureFiberRelation p q) ∧
    (∃ p q : BinaryModule × TernarySquareGroup,
      binaryPureFiberRelation p q ∧ ¬binaryWCosetRelation W p q) ∧
    (∃ p q : BinaryModule × TernarySquareGroup,
      binaryWCosetRelation W p q ∧ p ≠ q)

def binaryTrivialLineSummand
    (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W U : Submodule BinaryField BinaryModule) : Prop :=
  Module.finrank BinaryField W = 1 ∧
    (∀ h : TernarySquareGroup, ∀ v : BinaryModule, v ∈ W → ρ h v = v) ∧
    IsCompl W U

def binaryFixedLineCommonBlocks
    (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W : Submodule BinaryField BinaryModule) : Prop :=
  Module.finrank BinaryField W = 1 ∧
    binaryStrictCommonRefinement ρ W ∧
    (∀ v : BinaryModule, ∀ h : TernarySquareGroup,
      binaryCommonBlockCard W v h = 2)

def binarySizeEightModuleHasFixedLine_claim31087 : Prop :=
  binaryCubicFactorization ∧
  Nat.card TernarySquareGroup = 9 ∧
  (∀ ρ : BinaryRepresentation, binarySemisimpleRepresentation ρ.1) ∧
  (∀ (M : Type*) [AddCommGroup M] [Module BinaryField M]
      [FiniteDimensional BinaryField M]
      (ρ : TernarySquareGroup → (M ≃ₗ[BinaryField] M)),
    binarySimpleModuleRepresentation ρ →
      (Module.finrank BinaryField M = 1 ∨ Module.finrank BinaryField M = 2)) ∧
  (∀ (M : Type*) [AddCommGroup M] [Module BinaryField M]
      [FiniteDimensional BinaryField M]
      (ρ : TernarySquareGroup → (M ≃ₗ[BinaryField] M)),
    binarySimpleModuleRepresentation ρ →
      Module.finrank BinaryField M = 1 →
      ∀ h : TernarySquareGroup, ∀ v : M, ρ h v = v) ∧
  (∀ ρ : BinaryRepresentation,
    binarySemisimpleRepresentation ρ.1 →
      ∃ W U : Submodule BinaryField BinaryModule,
        binaryTrivialLineSummand ρ.1 W U ∧
        binaryFixedLineCommonBlocks ρ.1 W)

end

end MathlibPlus.Open.ResearchFormalization.R1534.BinarySizeEight
