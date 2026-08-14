import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffee23712

abbrev W := ZMod 7 × ZMod 7
abbrev H := ZMod 7 × ZMod 3
abbrev G := W × H

/-- The scalar in the specified `F₇ ⋊ C₃` action. -/
def chi (h : H) : ZMod 7 := (2 : ZMod 7) ^ h.2.val

def hOne : H := (0, 0)

def hMul (h k : H) : H :=
  (h.1 + chi h * k.1, h.2 + k.2)

def hInv (h : H) : H :=
  (-((2 : ZMod 7) ^ (-h.2).val) * h.1, -h.2)

def wZero : W := (0, 0)

def wAdd (w x : W) : W := (w.1 + x.1, w.2 + x.2)

def wSub (w x : W) : W := (w.1 - x.1, w.2 - x.2)

def chiW (h : H) (w : W) : W :=
  (chi h * w.1, chi h * w.2)

def gMul (c d : G) : G :=
  (wAdd c.1 (chiW c.2 d.1), hMul c.2 d.2)

def gInv (c : G) : G :=
  (wSub wZero (chiW (hInv c.2) c.1), hInv c.2)

def profile (F : H → Equiv.Perm W) (c : G) : G :=
  (F c.2 c.1, c.2)

def profileInv (F : H → Equiv.Perm W) (c : G) : G :=
  ((F c.2).symm c.1, c.2)

def special (h : H) : G :=
  (wZero, hInv h)

def derivative (F : H → Equiv.Perm W) (h : H) (c : G) : G :=
  gMul (profile F (gMul c (special h))) (gInv (profile F (special h)))

def delta (F : H → Equiv.Perm W) (h : H) (c : G) : G :=
  profileInv F (derivative F h c)

/-- Exact derivative computation for the origin-fixing profiles in Claim 43902. -/
def claim43902 : Prop :=
  ∀ (F : H → Equiv.Perm W),
    F hOne = Equiv.refl W →
    (∀ h : H, F h wZero = wZero) →
    ∀ (w : W) (h : H),
      let c : G := (w, h)
      gMul c (special h) = (w, hOne) ∧
      profile F (gMul c (special h)) = (w, hOne) ∧
      profile F (special h) = (wZero, hInv h) ∧
      derivative F h c = (w, h) ∧
      delta F h c = ((F h).symm w, h)

/-- Exact marked-offset derivative formula when origin-fixing is not assumed. -/
def claim43904 : Prop :=
  ∀ (F : H → Equiv.Perm W),
    F hOne = Equiv.refl W →
    ∀ (w : W) (h : H),
      delta F h (w, h) =
        ((F h).symm (wSub w (chiW h (F (hInv h) wZero))), h)

end MathlibPlus.Open.ResearchFormalization.Batch019ffee23712
