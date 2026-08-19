import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1441.Claim37225

noncomputable section

abbrev Field7 := ZMod 7
abbrev H := ZMod 7 × ZMod 3
abbrev W := ZMod 7 × ZMod 7
abbrev DualW := Module.Dual Field7 W
abbrev IncidenceIndex := Fin 8

/-- The matching-scalar semidirect multiplication on `H = C₇ ⋊ C₃`. -/
def hMul (h k : H) : H :=
  (h.1 + (2 : ZMod 7) ^ h.2.val * k.1, h.2 + k.2)

/-- The matching scalar action of `H` on `W = F₇²`. -/
def hScalar (h : H) (w : W) : W :=
  ((2 : ZMod 7) ^ h.2.val * w.1,
    (2 : ZMod 7) ^ h.2.val * w.2)

/-- The inverse for the displayed semidirect multiplication. -/
def hInv (h : H) : H :=
  (-((2 : ZMod 7) ^ (-h.2).val) * h.1, -h.2)

def hPow (h : H) : ℕ → H
  | 0 => (0, 0)
  | n + 1 => hMul (hPow h n) h

def hIsSubgroup (K : Set H) : Prop :=
  (0, 0) ∈ K ∧
    (∀ x y : H, x ∈ K → y ∈ K → hMul x y ∈ K) ∧
      (∀ x : H, x ∈ K → hInv x ∈ K)

/-- The normal `C₇` class and the seven complement `C₃` classes. -/
def classGenerator (K : IncidenceIndex) : H :=
  if K.val = 0 then (1, 0)
  else (((K.val - 1 : ℕ) : ZMod 7), 1)

def classCarrier (K : IncidenceIndex) : Set H :=
  Set.range (hPow (classGenerator K))

def derivativeDefect (τ : H → W) (h k : H) : W :=
  τ (hMul h k) - τ h - hScalar h (τ k)

def derivativeSubspace (τ : H → W) (h : H) : Submodule Field7 W :=
  Submodule.span Field7 (Set.range (derivativeDefect τ h))

def dualFirst : DualW :=
  LinearMap.fst Field7 Field7 Field7

def dualSecond : DualW :=
  LinearMap.snd Field7 Field7 Field7

/-- The eight normalized representatives of the projective normal lines in
`P(W*)`: the vertical line and the seven affine slopes. -/
def normalFunctional (N : IncidenceIndex) : DualW :=
  if N.val = 0 then dualSecond
  else dualFirst + ((N.val - 1 : ℕ) : ZMod 7) • dualSecond

def normalLine (N : IncidenceIndex) : Submodule Field7 DualW :=
  Submodule.span Field7 ({normalFunctional N} : Set DualW)

def normalAnnihilates
    (N : IncidenceIndex) (D : Submodule Field7 W) : Prop :=
  ∀ φ : normalLine N, ∀ w : D, φ.1 w.1 = 0

/-- Activity of a projective normal on a cyclic-class row. -/
def active (τ : H → W) (K N : IncidenceIndex) : Prop :=
  normalAnnihilates N (derivativeSubspace τ (classGenerator K))

def scalarCocycleLocus (τ : H → W) (N : IncidenceIndex) : Set H :=
  {h | ∀ k : H,
    normalFunctional N (derivativeDefect τ h k) = 0}

def projectiveCocycle (τ : H → W) (N : IncidenceIndex) : Prop :=
  ∀ h k : H, normalFunctional N (derivativeDefect τ h k) = 0

def generatedBy (K₁ K₂ : IncidenceIndex) : Set H :=
  {h | ∀ U : Set H,
    hIsSubgroup U → classCarrier K₁ ⊆ U → classCarrier K₂ ⊆ U → h ∈ U}

def fullRow (τ : H → W) (K : IncidenceIndex) : Prop :=
  ∀ N : IncidenceIndex, active τ K N

def fullColumn (τ : H → W) (N : IncidenceIndex) : Prop :=
  ∀ K : IncidenceIndex, active τ K N

def normalizedTranslation (τ : H → W) : Prop :=
  τ (0, 0) = 0

/-- Claim 37225: distinct active normals in one cyclic-class row span `W*`
and fill that row; one normal active on two distinct classes has a subgroup
cocycle locus, and the generated classes fill the normal column. -/
def claim37225 : Prop :=
  (∀ K : IncidenceIndex,
    classGenerator K ≠ (0, 0) ∧ hIsSubgroup (classCarrier K)) ∧
    (∀ τ : H → W,
      normalizedTranslation τ →
        (∀ K N₁ N₂ : IncidenceIndex,
          N₁ ≠ N₂ →
            active τ K N₁ →
              active τ K N₂ →
                normalLine N₁ ⊔ normalLine N₂ = ⊤ ∧
                  fullRow τ K) ∧
        (∀ N K₁ K₂ : IncidenceIndex,
          K₁ ≠ K₂ →
            active τ K₁ N →
              active τ K₂ N →
                generatedBy K₁ K₂ = Set.univ ∧
                  hIsSubgroup (scalarCocycleLocus τ N) ∧
                    scalarCocycleLocus τ N = Set.univ ∧
                      projectiveCocycle τ N ∧
                        fullColumn τ N))

end

end MathlibPlus.Open.ResearchFormalization.R1441.Claim37225
