import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1575Claim39301

noncomputable section

abbrev F7 := ZMod 7
abbrev F3 := ZMod 3
abbrev H := F7 × F3
abbrev W := F7 × F7
abbrev HeisenbergPoint := F7 × F7 × F7

/-- The coordinate carrier for the nonabelian `E(C₇,3)` factor.  Its
multiplication is `hMul`; the componentwise additive product on `H` is not
used as the group operation. -/
def scalar (i : F3) : F7 := (2 : F7) ^ i.val

def chi (h : H) : F7 := scalar h.2

def hOne : H := (0, 0)

def hMul (h k : H) : H := (h.1 + chi h * k.1, h.2 + k.2)

def hInv (h : H) : H := (-scalar (0 - h.2) * h.1, 0 - h.2)

def hC7Kernel : Set H := {h | h.2 = 0}

def hC3Complement : Set H := {h | h.1 = 0}

def hSubgroup (S : Set H) : Prop :=
  hOne ∈ S ∧
    (∀ h, h ∈ S → hInv h ∈ S) ∧
      ∀ h k, h ∈ S → k ∈ S → hMul h k ∈ S

def eC73Nonabelian : Prop :=
  hMul (1, 0) (0, 1) ≠ hMul (0, 1) (1, 0)

def chiCharacter : Prop :=
  chi hOne = 1 ∧ ∀ h k, chi (hMul h k) = chi h * chi k

def G := W × H

def gMul (g g' : G) : G :=
  (g.1 + chi g.2 • g'.1, hMul g.2 g'.2)

def coordinateN (w : W) : W := (w.2, 0)

def wZero : W := (0, 0)

def profile (lam : H → F7) (tau : H → W) (w : W) (h : H) : W × H :=
  (w + lam h • coordinateN w + tau h, h)

def normalizedProfile (lam : H → F7) (tau : H → W) : Prop :=
  lam hOne = 0 ∧ tau hOne = wZero

def defect (tau : H → W) (h k : H) : W :=
  tau (hMul h k) - tau h - chi h • tau k

def profileInversePart (lam : H → F7) (h : H) (w : W) : W :=
  w - lam h • coordinateN w

def derivativeFiber (lam : H → F7) (tau : H → W)
    (h k : H) (x w : W) : W :=
  (w + (lam (hMul h k) - lam h) • coordinateN w) +
    (chi h * (lam (hMul h k) - lam k)) • coordinateN x +
      profileInversePart lam h (defect tau h k)

def leftPeriod (lam : H → F7) : Set H :=
  {h | ∀ k, lam (hMul h k) = lam k}

def heisOne : HeisenbergPoint := (0, 0, 0)

def heisMul (g g' : HeisenbergPoint) : HeisenbergPoint :=
  (g.1 + g'.1, g.2.1 + g'.2.1 + g.1 * g'.2.2, g.2.2 + g'.2.2)

def heisInv (g : HeisenbergPoint) : HeisenbergPoint :=
  (-g.1, -g.2.1 + g.1 * g.2.2, -g.2.2)

def heisAction (g : HeisenbergPoint) (w : W) : W :=
  (w.1 + g.1 * w.2 + g.2.1, w.2 + g.2.2)

def heisCommutator (g g' : HeisenbergPoint) : HeisenbergPoint :=
  heisMul (heisMul g g') (heisMul (heisInv g) (heisInv g'))

def heisGroupLaws : Prop :=
  (∀ g g' g'' : HeisenbergPoint,
    heisMul (heisMul g g') g'' = heisMul g (heisMul g' g'')) ∧
    (∀ g : HeisenbergPoint,
      heisMul g heisOne = g ∧
        heisMul heisOne g = g ∧
          heisMul g (heisInv g) = heisOne ∧
            heisMul (heisInv g) g = heisOne)

def periodGenerator (lam : H → F7) (tau : H → W) (h k : H) : HeisenbergPoint :=
  (lam k, (defect tau h k).1, (defect tau h k).2)


def heisSubgroup (S : Set HeisenbergPoint) : Prop :=
  heisOne ∈ S ∧
    (∀ g, g ∈ S → heisInv g ∈ S) ∧
      ∀ g g', g ∈ S → g' ∈ S → heisMul g g' ∈ S

def heisGenerated (gens : Set HeisenbergPoint) : Set HeisenbergPoint :=
  {g | ∀ S : Set HeisenbergPoint, heisSubgroup S → gens ⊆ S → g ∈ S}

def heisOrbit (Gamma : Set HeisenbergPoint) (w : W) : Set W :=
  {v | ∃ g, g ∈ Gamma ∧ heisAction g w = v}

def translationStabilizer (Gamma : Set HeisenbergPoint) : Set W :=
  {t | ∀ w : W,
    Set.image (fun v : W => v + t) (heisOrbit Gamma w) = heisOrbit Gamma w}

def projection (g : HeisenbergPoint) : W := (g.1, g.2.2)

def projectionSubmodule (Gamma : Set HeisenbergPoint) : Submodule F7 W :=
  Submodule.span F7 {p : W | ∃ g, g ∈ Gamma ∧ projection g = p}

def projectionDimension (Gamma : Set HeisenbergPoint) : Nat :=
  Module.finrank F7 (projectionSubmodule Gamma : Type)

def translationU : Set W := {w | w.2 = 0}

def heisenbergU : Set HeisenbergPoint :=
  {g | g.1 = 0 ∧ g.2.2 = 0}

def heisenbergZero : Set HeisenbergPoint := {heisOne}

def verticalProjectionNonzero (Gamma : Set HeisenbergPoint) : Prop :=
  ∃ g, g ∈ Gamma ∧ g.2.2 ≠ 0

def heisPow (g : HeisenbergPoint) : Nat → HeisenbergPoint
  | 0 => heisOne
  | n + 1 => heisMul (heisPow g n) g

def heisCyclicOrderSeven (Gamma : Set HeisenbergPoint) : Prop :=
  ∃ g : HeisenbergPoint,
    Gamma = {x | ∃ n : Fin 7, heisPow g n.val = x} ∧
      Set.ncard Gamma = 7

def periodFiberSubgroup (lam : H → F7) (tau : H → W) (h : H) :
    Set HeisenbergPoint :=
  heisGenerated (Set.range (periodGenerator lam tau h))

/-- Claim 39301: the common translation stabilizer has the exact three-way
trichotomy on the generated period-fiber Heisenberg subgroup. -/
def claim_39301 : Prop :=
  ∀ (lam : H → F7) (tau : H → W) (h : H),
    normalizedProfile lam tau →
      h ∈ leftPeriod lam →
        (∃ k : H, lam k ≠ 0) →
          let Gamma := periodFiberSubgroup lam tau h
          let T := translationStabilizer Gamma
          let Pdim := projectionDimension Gamma
          (Pdim = 2 ∧ T = Set.univ) ∨
            (Pdim = 1 ∧
              (Gamma ∩ heisenbergU = heisenbergU) ∧
                ((verticalProjectionNonzero Gamma ∧ T = Set.univ) ∨
                  (¬ verticalProjectionNonzero Gamma ∧ T = translationU)) ) ∨
              (Pdim = 1 ∧
                Gamma ∩ heisenbergU = heisenbergZero ∧
                  T = {wZero} ∧ heisCyclicOrderSeven Gamma)

end

end MathlibPlus.Open.ResearchFormalization.R1575Claim39301
