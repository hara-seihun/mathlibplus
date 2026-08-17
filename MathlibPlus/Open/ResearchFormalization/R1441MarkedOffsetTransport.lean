import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

noncomputable section

abbrev H := ZMod 7 × ZMod 3
abbrev W := ZMod 7 × ZMod 7

def hMul (h k : H) : H :=
  (h.1 + (2 : ZMod 7) ^ h.2.val * k.1, h.2 + k.2)

def hScalar (h : H) (w : W) : W :=
  ((2 : ZMod 7) ^ h.2.val * w.1,
    (2 : ZMod 7) ^ h.2.val * w.2)

def normalizedRelativeDerivative
    (F : H → Equiv.Perm W) (h k : H) (x w : W) : W :=
  (F h).symm
    (F (hMul h k) (w + hScalar h x) - hScalar h (F k x))

def derivativeGeneratorSet
    (F : H → Equiv.Perm W) (h : H) : Set (W → W) :=
  {d | ∃ k : H, ∃ x : W,
    d = normalizedRelativeDerivative F h k x}

def derivativeOrbit
    (F : H → Equiv.Perm W) (h : H) (w : W) : Set W :=
  {v | Relation.EqvGen (fun x y : W =>
      ∃ k : H, ∃ z : W,
        y = normalizedRelativeDerivative F h k z x) w v}

def derivativeOrbitPartition
    (F : H → Equiv.Perm W) (h : H) : Set (Set W) :=
  {O | ∃ w : W, O = derivativeOrbit F h w}

def rowOffset (F : H → Equiv.Perm W) (h : H) : W :=
  F h 0

def rowTranslation (c : W) (O : Set W) : Set W :=
  Set.image (fun w => w + c) O

/-- Claim 37233: every exact normalized-relative-derivative orbit in a
quotient row is transported by that row's single marked offset. -/
def claim37233_uniformMarkedOffsetTransport : Prop :=
  ∀ (F : H → Equiv.Perm W),
    F (0, 0) = Equiv.refl W →
      ∀ h : H, ∀ O : Set W,
        O ∈ derivativeOrbitPartition F h →
          Set.image (F h) O = rowTranslation (rowOffset F h) O

end

end MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport
