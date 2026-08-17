import Mathlib
import MathlibPlus.Open.CayleyCIE7

namespace MathlibPlus.Open.ResearchFormalization.R1441Claim37224

noncomputable section

abbrev H := MathlibPlus.Open.CayleyCIE7.E_C7_3
abbrev W := ZMod 7 × ZMod 7
abbrev Dual := W →ₗ[ZMod 7] ZMod 7

/-- The matching scalar character and its action on the exact rank-two layer. -/
def chi (h : H) : ZMod 7 :=
  MathlibPlus.Open.CayleyCIE7.actionTwoPower h.2

def hAction (h : H) (w : W) : W :=
  (chi h * w.1, chi h * w.2)

/-- The normalized derivative defect in the pure-translation profile. -/
def derivativeDefect (τ : H → W) (h k : H) : W :=
  τ (MathlibPlus.Open.CayleyCIE7.eC73Mul h k) - τ h - hAction h (τ k)

def derivativeSubspace (τ : H → W) (h : H) : Submodule (ZMod 7) W :=
  Submodule.span (ZMod 7) (Set.range (derivativeDefect τ h))

def normalizedProfile (τ : H → W) : Prop :=
  τ MathlibPlus.Open.CayleyCIE7.eC73One = 0

/-- The eight actual cyclic-subgroup classes: class zero is the normal C7,
and classes one through seven are the seven C3 complements. -/
def cyclicClassGenerator (K : Fin 8) : H :=
  if K.val = 0 then
    (1, 0)
  else
    ((K.val - 1 : ℕ), 1)

def hPow : H → ℕ → H
  | _, 0 => MathlibPlus.Open.CayleyCIE7.eC73One
  | h, n + 1 =>
      MathlibPlus.Open.CayleyCIE7.eC73Mul (hPow h n) h

def cyclicClassCarrier (K : Fin 8) : Set H :=
  {h | ∃ n : Fin (if K.val = 0 then 7 else 3),
    h = hPow (cyclicClassGenerator K) n.val}

def nonidentityCyclicClassCarrier (K : Fin 8) : Set H :=
  cyclicClassCarrier K \ {MathlibPlus.Open.CayleyCIE7.eC73One}

def exactCyclicClassPartition : Prop :=
  (Nat.card (Fin 8) = 8) ∧
    (∀ K : Fin 8,
      Set.ncard (cyclicClassCarrier K) = if K.val = 0 then 7 else 3) ∧
    (∀ K L : Fin 8, K ≠ L →
      Disjoint (nonidentityCyclicClassCarrier K)
        (nonidentityCyclicClassCarrier L)) ∧
    (∀ h : H, h ≠ MathlibPlus.Open.CayleyCIE7.eC73One →
      ∃! K : Fin 8, h ∈ nonidentityCyclicClassCarrier K)

/-- Canonical representatives for the projective lines in the dual W*. -/
def normalizedProjectiveNormal (n : Dual) : Prop :=
  n ≠ 0 ∧
    (n (1, 0) = 1 ∨ (n (1, 0) = 0 ∧ n (0, 1) = 1))

abbrev ProjectiveNormal := {n : Dual // normalizedProjectiveNormal n}

def projectiveNormalCount : Prop :=
  Nat.card ProjectiveNormal = 8

def annihilates (n : Dual) (D : Submodule (ZMod 7) W) : Prop :=
  ∀ w : W, w ∈ D → n w = 0

def activePair (τ : H → W) (K : Fin 8) (n : ProjectiveNormal) : Prop :=
  annihilates n.1 (derivativeSubspace τ (cyclicClassGenerator K))

def scalarCochain (τ : H → W) (n : ProjectiveNormal) (h : H) : ZMod 7 :=
  n.1 (τ h)

/-- The scalar equation attached to one nonidentity generator and all right
multipliers, exactly the equation in the source statement. -/
def scalarRowCocycle (τ : H → W) (n : ProjectiveNormal) (h : H) : Prop :=
  ∀ k : H,
    scalarCochain τ n
        (MathlibPlus.Open.CayleyCIE7.eC73Mul h k) =
      scalarCochain τ n h + chi h * scalarCochain τ n k

def generatorIndependent (τ : H → W) (K : Fin 8) (n : ProjectiveNormal) : Prop :=
  ∀ h : H, h ∈ nonidentityCyclicClassCarrier K →
    (annihilates n.1 (derivativeSubspace τ h) ↔ activePair τ K n) ∧
    (scalarRowCocycle τ n h ↔ activePair τ K n)

/-- Claim 37224: exact cyclic-class/projective-normal incidence and its
row-cocycle characterization. -/
def claim37224 : Prop :=
  exactCyclicClassPartition ∧
    projectiveNormalCount ∧
    ∀ (τ : H → W), normalizedProfile τ →
      ∀ (K : Fin 8) (n : ProjectiveNormal),
        (activePair τ K n ↔
          scalarRowCocycle τ n (cyclicClassGenerator K)) ∧
        generatorIndependent τ K n

end
end MathlibPlus.Open.ResearchFormalization.R1441Claim37224
