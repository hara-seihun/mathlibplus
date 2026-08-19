import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1534.PureRepresentationRefinement

noncomputable section

abbrev BinaryField := ZMod 2
abbrev BinaryModule := Fin 3 → BinaryField
abbrev TernarySquareGroup := Multiplicative (ZMod 3 × ZMod 3)
abbrev BinaryGeneralLinear := BinaryModule ≃ₗ[BinaryField] BinaryModule
abbrev BinaryRepresentation :=
  {ρ : TernarySquareGroup → BinaryGeneralLinear //
    ρ 1 = 1 ∧ ∀ x y : TernarySquareGroup, ρ (x * y) = ρ x * ρ y}

abbrev TernaryField := ZMod 3
abbrev TernaryModule := Fin 2 → TernaryField
abbrev BinaryCubeGroup := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)
abbrev TernaryGeneralLinear := TernaryModule ≃ₗ[TernaryField] TernaryModule
abbrev TernaryRepresentation :=
  {ρ : BinaryCubeGroup → TernaryGeneralLinear //
    ρ 1 = 1 ∧ ∀ x y : BinaryCubeGroup, ρ (x * y) = ρ x * ρ y}

abbrev MixedProductGroup := BinaryCubeGroup × TernarySquareGroup
abbrev BinaryPureCarrier := BinaryModule × TernarySquareGroup
abbrev TernaryPureCarrier := TernaryModule × BinaryCubeGroup

def binaryTwistedMap (ρ : BinaryRepresentation) :
    BinaryPureCarrier → BinaryPureCarrier :=
  fun p => (ρ.1 p.2 p.1, p.2)

def ternaryTwistedMap (ρ : TernaryRepresentation) :
    TernaryPureCarrier → TernaryPureCarrier :=
  fun p => (ρ.1 p.2 p.1, p.2)

def binaryPureFiberBlock (h : TernarySquareGroup) : Set BinaryPureCarrier :=
  {p | p.2 = h}

def ternaryPureFiberBlock (h : BinaryCubeGroup) : Set TernaryPureCarrier :=
  {p | p.2 = h}

def binaryPureFiberBlockCard (h : TernarySquareGroup) : ℕ :=
  Nat.card {p : BinaryPureCarrier // p ∈ binaryPureFiberBlock h}

def ternaryPureFiberBlockCard (h : BinaryCubeGroup) : ℕ :=
  Nat.card {p : TernaryPureCarrier // p ∈ ternaryPureFiberBlock h}

def binaryRepresentationTwistedPureSystem (ρ : BinaryRepresentation) : Prop :=
  (∀ h : TernarySquareGroup, binaryPureFiberBlockCard h = 8) ∧
    (∀ p : BinaryPureCarrier, (binaryTwistedMap ρ p).2 = p.2)

def ternaryRepresentationTwistedPureSystem (ρ : TernaryRepresentation) : Prop :=
  (∀ h : BinaryCubeGroup, ternaryPureFiberBlockCard h = 9) ∧
    (∀ p : TernaryPureCarrier, (ternaryTwistedMap ρ p).2 = p.2)

def binarySourceOrbitBlock (W : Submodule BinaryField BinaryModule)
    (v : BinaryModule) (h : TernarySquareGroup) : Set BinaryPureCarrier :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (w : BinaryModule)}

def binaryPulledBackTargetOrbitBlock
    (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W : Submodule BinaryField BinaryModule) (v : BinaryModule)
    (h : TernarySquareGroup) : Set BinaryPureCarrier :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (ρ h).symm (w : BinaryModule)}

def binaryPureFiberRelation : BinaryPureCarrier → BinaryPureCarrier → Prop :=
  fun p q => p.2 = q.2

def binaryWCosetRelation (W : Submodule BinaryField BinaryModule) :
    BinaryPureCarrier → BinaryPureCarrier → Prop :=
  fun p q =>
    p.2 = q.2 ∧ ∃ w₁ w₂ : W,
      p.1 + (w₁ : BinaryModule) = q.1 + (w₂ : BinaryModule)

def binaryCommonBlockCard (W : Submodule BinaryField BinaryModule)
    (v : BinaryModule) (h : TernarySquareGroup) : ℕ :=
  Nat.card {p : BinaryPureCarrier // p ∈ binarySourceOrbitBlock W v h}

def binaryStrictCommonRefinement
    (ρ : TernarySquareGroup → BinaryGeneralLinear)
    (W : Submodule BinaryField BinaryModule) : Prop :=
  W ≠ ⊥ ∧ W ≠ ⊤ ∧
    (∀ h : TernarySquareGroup,
      Submodule.map (ρ h).toLinearMap W = W) ∧
    (∀ v : BinaryModule, ∀ h : TernarySquareGroup,
      binarySourceOrbitBlock W v h = binaryPulledBackTargetOrbitBlock ρ W v h) ∧
    (∀ p q : BinaryPureCarrier,
      binaryWCosetRelation W p q → binaryPureFiberRelation p q) ∧
    (∀ v : BinaryModule, ∀ h : TernarySquareGroup,
      binarySourceOrbitBlock W v h ⊆ binaryPureFiberBlock h) ∧
    (∃ p q : BinaryPureCarrier,
      binaryPureFiberRelation p q ∧ ¬binaryWCosetRelation W p q) ∧
    (∃ p q : BinaryPureCarrier,
      binaryWCosetRelation W p q ∧ p ≠ q)

def ternarySourceOrbitBlock (W : Submodule TernaryField TernaryModule)
    (v : TernaryModule) (h : BinaryCubeGroup) : Set TernaryPureCarrier :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (w : TernaryModule)}

def ternaryPulledBackTargetOrbitBlock
    (ρ : BinaryCubeGroup → TernaryGeneralLinear)
    (W : Submodule TernaryField TernaryModule) (v : TernaryModule)
    (h : BinaryCubeGroup) : Set TernaryPureCarrier :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (ρ h).symm (w : TernaryModule)}

def ternaryPureFiberRelation : TernaryPureCarrier → TernaryPureCarrier → Prop :=
  fun p q => p.2 = q.2

def ternaryWCosetRelation (W : Submodule TernaryField TernaryModule) :
    TernaryPureCarrier → TernaryPureCarrier → Prop :=
  fun p q =>
    p.2 = q.2 ∧ ∃ w₁ w₂ : W,
      p.1 + (w₁ : TernaryModule) = q.1 + (w₂ : TernaryModule)

def ternaryCommonBlockCard (W : Submodule TernaryField TernaryModule)
    (v : TernaryModule) (h : BinaryCubeGroup) : ℕ :=
  Nat.card {p : TernaryPureCarrier // p ∈ ternarySourceOrbitBlock W v h}

def ternaryStrictCommonRefinement
    (ρ : BinaryCubeGroup → TernaryGeneralLinear)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  W ≠ ⊥ ∧ W ≠ ⊤ ∧
    (∀ h : BinaryCubeGroup,
      Submodule.map (ρ h).toLinearMap W = W) ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternarySourceOrbitBlock W v h = ternaryPulledBackTargetOrbitBlock ρ W v h) ∧
    (∀ p q : TernaryPureCarrier,
      ternaryWCosetRelation W p q → ternaryPureFiberRelation p q) ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternarySourceOrbitBlock W v h ⊆ ternaryPureFiberBlock h) ∧
    (∃ p q : TernaryPureCarrier,
      ternaryPureFiberRelation p q ∧ ¬ternaryWCosetRelation W p q) ∧
    (∃ p q : TernaryPureCarrier,
      ternaryWCosetRelation W p q ∧ p ≠ q)

def binaryCommonPrimeRefinement
    (ρ : BinaryRepresentation)
    (W : Submodule BinaryField BinaryModule) : Prop :=
  Module.finrank BinaryField W = 1 ∧
    binaryStrictCommonRefinement ρ.1 W ∧
    (∀ v : BinaryModule, ∀ h : TernarySquareGroup,
      binaryCommonBlockCard W v h = 2)

def ternaryCommonPrimeRefinement
    (ρ : TernaryRepresentation)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  Module.finrank TernaryField W = 1 ∧
    ternaryStrictCommonRefinement ρ.1 W ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternaryCommonBlockCard W v h = 3)

def binaryPureSystemIsMinimumNontrivialCommonBlockSystem
    (ρ : BinaryRepresentation) : Prop :=
  ¬∃ W : Submodule BinaryField BinaryModule, binaryCommonPrimeRefinement ρ W

def ternaryPureSystemIsMinimumNontrivialCommonBlockSystem
    (ρ : TernaryRepresentation) : Prop :=
  ¬∃ W : Submodule TernaryField TernaryModule, ternaryCommonPrimeRefinement ρ W

def pureRepresentationRefinementClaim31089 : Prop :=
  (∀ ρ : BinaryRepresentation,
    binaryRepresentationTwistedPureSystem ρ ∧
      (∃ W : Submodule BinaryField BinaryModule,
        binaryCommonPrimeRefinement ρ W ∧
        ¬binaryPureSystemIsMinimumNontrivialCommonBlockSystem ρ)) ∧
  (∀ ρ : TernaryRepresentation,
    ternaryRepresentationTwistedPureSystem ρ ∧
      (∃ W : Submodule TernaryField TernaryModule,
        ternaryCommonPrimeRefinement ρ W ∧
        ¬ternaryPureSystemIsMinimumNontrivialCommonBlockSystem ρ))

end

end MathlibPlus.Open.ResearchFormalization.R1534.PureRepresentationRefinement
