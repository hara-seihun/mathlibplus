import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1534.RepresentationCensusF3

noncomputable section

abbrev TernaryField := ZMod 3
abbrev TernaryModule := Fin 2 → TernaryField
abbrev BinaryCubeGroup := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)
abbrev TernaryMatrixGroup := Matrix.GeneralLinearGroup (Fin 2) TernaryField

abbrev TernaryRepresentation :=
  {ρ : BinaryCubeGroup → TernaryMatrixGroup //
    ρ 1 = 1 ∧ ∀ x y : BinaryCubeGroup, ρ (x * y) = ρ x * ρ y}

def ternaryMatrixAction (A : TernaryMatrixGroup) :
    TernaryModule ≃ₗ[TernaryField] TernaryModule :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv

def ternaryInvariantSubmodule (ρ : TernaryRepresentation)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  ∀ h : BinaryCubeGroup,
    Submodule.map (ternaryMatrixAction (ρ.1 h)).toLinearMap W = W

def ternaryInvariantLine (ρ : TernaryRepresentation)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  Module.finrank TernaryField W = 1 ∧ ternaryInvariantSubmodule ρ W

def ternaryInvariantLineCount (ρ : TernaryRepresentation) : ℕ :=
  Nat.card {W : Submodule TernaryField TernaryModule // ternaryInvariantLine ρ W}

def ternaryImageOrder (ρ : TernaryRepresentation) : ℕ :=
  Nat.card (Set.range ρ.1)

def ternarySourceOrbitBlock (W : Submodule TernaryField TernaryModule)
    (v : TernaryModule) (h : BinaryCubeGroup) : Set (TernaryModule × BinaryCubeGroup) :=
  {p | p.2 = h ∧ ∃ w : W, p.1 = v + (w : TernaryModule)}

def ternaryPulledBackTargetOrbitBlock
    (ρ : TernaryRepresentation)
    (W : Submodule TernaryField TernaryModule) (v : TernaryModule)
    (h : BinaryCubeGroup) : Set (TernaryModule × BinaryCubeGroup) :=
  {p | p.2 = h ∧ ∃ w : W,
    p.1 = v + (ternaryMatrixAction (ρ.1 h)).symm (w : TernaryModule)}

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

def ternaryCommonPrimeRefinement
    (ρ : TernaryRepresentation)
    (W : Submodule TernaryField TernaryModule) : Prop :=
  Module.finrank TernaryField W = 1 ∧
    W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ternaryInvariantSubmodule ρ W ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternarySourceOrbitBlock W v h = ternaryPulledBackTargetOrbitBlock ρ W v h) ∧
    (∀ p q : TernaryModule × BinaryCubeGroup,
      ternaryWCosetRelation W p q → ternaryPureFiberRelation p q) ∧
    (∀ v : TernaryModule, ∀ h : BinaryCubeGroup,
      ternaryCommonBlockCard W v h = 3) ∧
    (∃ p q : TernaryModule × BinaryCubeGroup,
      ternaryPureFiberRelation p q ∧ ¬ternaryWCosetRelation W p q) ∧
    (∃ p q : TernaryModule × BinaryCubeGroup,
      ternaryWCosetRelation W p q ∧ p ≠ q)

def ternaryCommonPrimeRefinementCount
    (ρ : TernaryRepresentation) : ℕ :=
  Nat.card {W : Submodule TernaryField TernaryModule //
    ternaryCommonPrimeRefinement ρ W}

def exactFiniteRepresentationCensus_claim31091 : Prop :=
  Fintype.card TernaryRepresentation = 344 ∧
  (Finset.univ.filter (fun ρ : TernaryRepresentation =>
    ternaryImageOrder ρ = 1)).card = 1 ∧
  (Finset.univ.filter (fun ρ : TernaryRepresentation =>
    ternaryImageOrder ρ = 2)).card = 91 ∧
  (Finset.univ.filter (fun ρ : TernaryRepresentation =>
    ternaryImageOrder ρ = 4)).card = 252 ∧
  (Finset.univ.filter (fun ρ : TernaryRepresentation =>
    ternaryInvariantLineCount ρ = 2)).card = 336 ∧
  (Finset.univ.filter (fun ρ : TernaryRepresentation =>
    ternaryInvariantLineCount ρ = 4)).card = 8 ∧
  (∀ ρ : TernaryRepresentation, ¬Function.Injective ρ.1) ∧
  (∀ ρ : TernaryRepresentation, 0 < ternaryInvariantLineCount ρ) ∧
  (∑ ρ : TernaryRepresentation, ternaryCommonPrimeRefinementCount ρ) = 704

end

end MathlibPlus.Open.ResearchFormalization.R1534.RepresentationCensusF3
