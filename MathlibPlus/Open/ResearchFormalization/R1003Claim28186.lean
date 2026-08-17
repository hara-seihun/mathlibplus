import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28186

abbrev HCoordinate : Type := ZMod 5 × ZMod 8
abbrev GCoordinate : Type := ZMod 7 × HCoordinate
abbrev OmegaH : Type := ZMod 8 × ZMod 5
abbrev Omega : Type := ZMod 7 × OmegaH

def hMul (a b : HCoordinate) : HCoordinate :=
  (a.1 + (-1 : ZMod 5) ^ a.2.val * b.1, a.2 + b.2)

def gMul (a b : GCoordinate) : GCoordinate :=
  (a.1 + (-1 : ZMod 7) ^ a.2.2.val * b.1, hMul a.2 b.2)

def hOne : HCoordinate := (0, 0)

def basePermutation (i : ZMod 8) : ZMod 8 :=
  if i = 0 then 0 else
    if i = 1 then 1 else
      if i = 2 then 6 else
        if i = 3 then 7 else
          if i = 4 then 4 else
            if i = 5 then 5 else
              if i = 6 then 2 else 3

def baseLabel1 (h : HCoordinate) : OmegaH :=
  (h.2, (-1 : ZMod 5) ^ h.2.val * h.1)

def baseLabel2 (h : HCoordinate) : OmegaH :=
  (basePermutation h.2, (-1 : ZMod 5) ^ h.2.val * h.1)

def lambda1 (g : GCoordinate) : Omega :=
  (g.1, baseLabel1 g.2)

def lambda2 (t : HCoordinate → ZMod 7) (g : GCoordinate) : Omega :=
  (g.1 + t g.2, baseLabel2 g.2)

def transportedRightRegular (lab : GCoordinate → Omega) :
    Set (Equiv.Perm Omega) :=
  {p | ∃ a : GCoordinate, ∀ z : GCoordinate,
    p (lab z) = lab (gMul z a)}

def P : Set (Equiv.Perm Omega) := transportedRightRegular lambda1

def Q (t : HCoordinate → ZMod 7) : Set (Equiv.Perm Omega) :=
  transportedRightRegular (lambda2 t)

def generatedPair (t : HCoordinate → ZMod 7) :
    Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure (P ∪ Q t)

def rootBase : OmegaH := baseLabel1 hOne

def root : Omega := (0, rootBase)

def pointStabilizer (t : HCoordinate → ZMod 7) :
    Set (Equiv.Perm Omega) :=
  {p | p ∈ generatedPair t ∧ p root = root}

def nonzeroNormalizedOneSupport (t : HCoordinate → ZMod 7) : Prop :=
  t hOne = 0 ∧
    ∃ h : HCoordinate, h ≠ hOne ∧ t h ≠ 0 ∧
      ∀ k : HCoordinate, k ≠ h → t k = 0

def baseTransportedRightRegular (lab : HCoordinate → OmegaH) :
    Set (Equiv.Perm OmegaH) :=
  {p | ∃ a : HCoordinate, ∀ z : HCoordinate,
    p (lab z) = lab (hMul z a)}

def baseP : Set (Equiv.Perm OmegaH) :=
  baseTransportedRightRegular baseLabel1

def baseQ : Set (Equiv.Perm OmegaH) :=
  baseTransportedRightRegular baseLabel2

def baseGeneratedPair : Subgroup (Equiv.Perm OmegaH) :=
  Subgroup.closure (baseP ∪ baseQ)

def directedOrbital {A : Type*}
    (K : Subgroup (Equiv.Perm A)) (u v : A) : Set (A × A) :=
  {p | ∃ g : K,
    p = ((g : Equiv.Perm A) u, (g : Equiv.Perm A) v)}

def transposeRelation {A : Type*}
    (D : Set (A × A)) : Set (A × A) :=
  {p | (p.2, p.1) ∈ D}

def pairedOrbital {A : Type*}
    (K : Subgroup (Equiv.Perm A)) (u v : A) : Set (A × A) :=
  directedOrbital K u v ∪ transposeRelation (directedOrbital K u v)

def pairedOrbitals {A : Type*}
    (K : Subgroup (Equiv.Perm A)) : Set (Set (A × A)) :=
  {O | ∃ u v : A, u ≠ v ∧ O = pairedOrbital K u v}

def basePairedOrbitals : Set (Set (OmegaH × OmegaH)) :=
  pairedOrbitals baseGeneratedPair

def fullC7Lift (B : Set (OmegaH × OmegaH)) :
    Set (Omega × Omega) :=
  {p | (p.1.2, p.2.2) ∈ B}

def fiberDifference (k : Fin 3) : ZMod 7 :=
  (k.val + 1 : ℕ)

def internalInverseOrbital (k : Fin 3) :
    Set (Omega × Omega) :=
  {p | p.1.2 = p.2.2 ∧
    (p.2.1 - p.1.1 = fiberDifference k ∨
      p.2.1 - p.1.1 = -fiberDifference k)}

def exact18PairedOrbitalDecomposition
    (t : HCoordinate → ZMod 7) : Prop :=
  Set.ncard basePairedOrbitals = 15 ∧
    pairedOrbitals (generatedPair t) =
      Set.range internalInverseOrbital ∪
        Set.image fullC7Lift basePairedOrbitals ∧
      Set.ncard (Set.range internalInverseOrbital) = 3 ∧
        Set.ncard (Set.image fullC7Lift basePairedOrbitals) = 15 ∧
          Set.ncard (pairedOrbitals (generatedPair t)) = 3 + 15 ∧
            Set.ncard (pairedOrbitals (generatedPair t)) = 18

/-- Claim 28186: for every nonzero one-support profile, the actual paired
orbitals are the three internal inverse pairs and the fifteen full lifts of
the fixed standard base paired orbitals, hence there are eighteen. -/
def exactPairedOrbitalDecomposition : Prop :=
  ∀ t : HCoordinate → ZMod 7,
    nonzeroNormalizedOneSupport t → exact18PairedOrbitalDecomposition t

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28186
