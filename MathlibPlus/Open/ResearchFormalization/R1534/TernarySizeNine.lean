import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1534.TernarySizeNine

noncomputable section

abbrev TernaryField := ZMod 3
abbrev TernaryModule := Fin 2 → TernaryField
abbrev BinaryCubeGroup := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)
abbrev TernaryGeneralLinear := TernaryModule ≃ₗ[TernaryField] TernaryModule

abbrev TernaryRepresentation :=
  {ρ : BinaryCubeGroup → TernaryGeneralLinear //
    ρ 1 = 1 ∧ ∀ x y : BinaryCubeGroup, ρ (x * y) = ρ x * ρ y}

def ternaryInvariantSubmodule (ρ : BinaryCubeGroup → TernaryGeneralLinear)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  ∀ h : BinaryCubeGroup,
    Submodule.map (ρ h).toLinearMap W = W

def ternarySourceOrbitBlock (W : Submodule TernaryField TernaryModule)
    (v : TernaryModule) (h : BinaryCubeGroup) : Set (TernaryModule × BinaryCubeGroup) :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (w : TernaryModule)}

def ternaryPulledBackTargetOrbitBlock
    (ρ : BinaryCubeGroup → TernaryGeneralLinear)
    (W : Submodule TernaryField TernaryModule) (v : TernaryModule)
    (h : BinaryCubeGroup) : Set (TernaryModule × BinaryCubeGroup) :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (ρ h).symm (w : TernaryModule)}

def ternaryPureFiberRelation :
    (TernaryModule × BinaryCubeGroup) →
      (TernaryModule × BinaryCubeGroup) → Prop :=
  fun p q => p.2 = q.2

def ternaryWCosetRelation (W : Submodule TernaryField TernaryModule) :
    (TernaryModule × BinaryCubeGroup) →
      (TernaryModule × BinaryCubeGroup) → Prop :=
  fun p q =>
    p.2 = q.2 ∧ ∃ w₁ w₂ : W,
      p.1 + (w₁ : TernaryModule) = q.1 + (w₂ : TernaryModule)

def ternaryCommonBlockCard (W : Submodule TernaryField TernaryModule)
    (v : TernaryModule) (h : BinaryCubeGroup) : ℕ :=
  Nat.card {p : TernaryModule × BinaryCubeGroup //
    p ∈ ternarySourceOrbitBlock W v h}

def ternaryStrictCommonRefinement
    (ρ : BinaryCubeGroup → TernaryGeneralLinear)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ternaryInvariantSubmodule ρ W ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternarySourceOrbitBlock W v h = ternaryPulledBackTargetOrbitBlock ρ W v h) ∧
    (∀ p q : TernaryModule × BinaryCubeGroup,
      ternaryWCosetRelation W p q → ternaryPureFiberRelation p q) ∧
    (∃ p q : TernaryModule × BinaryCubeGroup,
      ternaryPureFiberRelation p q ∧ ¬ternaryWCosetRelation W p q) ∧
    (∃ p q : TernaryModule × BinaryCubeGroup,
      ternaryWCosetRelation W p q ∧ p ≠ q)

def ternaryQuadraticRoots : Prop :=
  (1 : TernaryField) ≠ -1 ∧
    ∀ x : TernaryField, x ^ 2 - 1 = 0 ↔ x = 1 ∨ x = -1

def ternaryDiagonalizable (A : TernaryGeneralLinear) : Prop :=
  ∃ b : Module.Basis (Fin 2) TernaryField TernaryModule,
    ∃ d : Fin 2 → TernaryField,
      ∀ i : Fin 2, A (b i) = d i • b i

def ternarySimultaneouslyDiagonalizable
    (ρ : BinaryCubeGroup → TernaryGeneralLinear) : Prop :=
  ∃ b : Module.Basis (Fin 2) TernaryField TernaryModule,
    ∀ h : BinaryCubeGroup, ∃ d : Fin 2 → TernaryField,
      ∀ i : Fin 2, ρ h (b i) = d i • b i

def ternaryInvariantLineCommonBlocks
    (ρ : BinaryCubeGroup → TernaryGeneralLinear)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  Module.finrank TernaryField W = 1 ∧
    ternaryStrictCommonRefinement ρ W ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternaryCommonBlockCard W v h = 3)

def ternarySizeNineModuleHasInvariantLine_claim31088 : Prop :=
  ternaryQuadraticRoots ∧
  Nat.card BinaryCubeGroup = 8 ∧
  (∀ ρ : TernaryRepresentation,
    (∀ h : BinaryCubeGroup, ternaryDiagonalizable (ρ.1 h)) ∧
    (∀ h : BinaryCubeGroup, (ρ.1 h) * (ρ.1 h) = 1) ∧
    (∀ h k : BinaryCubeGroup, ρ.1 h * ρ.1 k = ρ.1 k * ρ.1 h) ∧
    ternarySimultaneouslyDiagonalizable ρ.1 ∧
    ∃ W : Submodule TernaryField TernaryModule,
      ternaryInvariantLineCommonBlocks ρ.1 W)

end

end MathlibPlus.Open.ResearchFormalization.R1534.TernarySizeNine
