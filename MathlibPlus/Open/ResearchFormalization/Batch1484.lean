import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch1484

/-- The explicit semidirect-product carrier and multiplication used by the
matching-scalar `E(C₇,3)` claims. -/
abbrev H : Type := ZMod 7 × ZMod 3

def hMul : H → H → H
  | (a, i), (b, j) => (a + (2 : ZMod 7) ^ i.val * b, i + j)

def hOne : H := (0, 0)

def matchingScalarCharacter : H → ZMod 7
  | (_, i) => (2 : ZMod 7) ^ i.val

abbrev W (d : Nat) : Type := Fin d → ZMod 7

def normalized (d : Nat) (τ : H → W d) : Prop := τ hOne = 0

def derivativeSpace (d : Nat) (τ : H → W d) (h : H) : Submodule (ZMod 7) (W d) :=
  Submodule.span (ZMod 7) (Set.range (fun k : H =>
    τ (hMul h k) - τ h - matchingScalarCharacter h • τ k))

def isCocycle (d : Nat) (z : H → W d) : Prop :=
  ∀ h k : H, z (hMul h k) = z h + matchingScalarCharacter h • z k

def globalCocycleShadow (d : Nat) (τ : H → W d) : Prop :=
  ∃ z : H → W d,
    isCocycle d z ∧ ∀ h : H, τ h - z h ∈ derivativeSpace d τ h

def rankThreeCocycleShadowCounterexample : Prop :=
  ∃ τ : H → W 3, normalized 3 τ ∧ ¬ globalCocycleShadow 3 τ

abbrev Vec3 := W 3

/-- The five vectors A,B,C,D,E in the explicit support-15 witness. -/
def witnessA : Vec3 := ![1, 4, 4]
def witnessB : Vec3 := ![1, 5, 4]
def witnessC : Vec3 := ![0, 0, 4]
def witnessD : Vec3 := ![0, 4, 6]
def witnessE : Vec3 := ![5, 1, 3]

def witnessRow0 : Fin 7 → Vec3 :=
  ![0, 0, witnessA, witnessB, witnessC, witnessD, witnessE]

def witnessRow1 : Fin 7 → Vec3 :=
  ![witnessA, witnessB, witnessC, witnessD, witnessE, 0, 0]

def witnessRow2 : Fin 7 → Vec3 :=
  ![witnessE, 0, 0, witnessA, witnessB, witnessC, witnessD]

def explicitTau : H → Vec3
  | (a, i) => match i.val with
    | 0 => witnessRow0 a
    | 1 => witnessRow1 a
    | _ => witnessRow2 a

def supportCard (d : Nat) (τ : H → W d) : Nat :=
  Fintype.card {h : H // τ h ≠ 0}

def explicitNormalizedSupport15Witness : Prop :=
  normalized 3 explicitTau ∧ supportCard 3 explicitTau = 15

def zeroExtendedTau (d : Nat) : H → W d :=
  fun h k => if hk : k.val < 3 then explicitTau h ⟨k.val, hk⟩ else 0

def zeroExtensionDerivativeSpaces : Prop :=
  ∀ (d : Nat), 3 < d → ∀ h : H, ∀ v : W d,
    v ∈ derivativeSpace d (zeroExtendedTau d) h ↔
      ∃ u : Vec3,
        u ∈ derivativeSpace 3 explicitTau h ∧
          ∀ k : Fin d,
            v k = if hk : k.val < 3 then u ⟨k.val, hk⟩ else 0

def zeroExtensionNoShadow : Prop :=
  (¬ globalCocycleShadow 3 explicitTau) ∧
    ∀ d : Nat, 3 < d →
      normalized d (zeroExtendedTau d) ∧
        ¬ globalCocycleShadow d (zeroExtendedTau d)

def zeroExtensionToEveryHigherMatchingScalarDimension : Prop :=
  zeroExtensionDerivativeSpaces ∧ zeroExtensionNoShadow

def project01 (v : Vec3) : W 2 := ![v 0, v 1]
def project02 (v : Vec3) : W 2 := ![v 0, v 2]
def project12 (v : Vec3) : W 2 := ![v 1, v 2]

def allTwoCoordinateProjectionsHaveShadows : Prop :=
  globalCocycleShadow 2 (fun h => project01 (explicitTau h)) ∧
    globalCocycleShadow 2 (fun h => project02 (explicitTau h)) ∧
    globalCocycleShadow 2 (fun h => project12 (explicitTau h))

end MathlibPlus.Open.ResearchFormalization.Batch1484
