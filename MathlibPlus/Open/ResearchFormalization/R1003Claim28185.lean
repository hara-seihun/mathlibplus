import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28185

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

def nonidentityBaseFibers : Set OmegaH :=
  {b | b ≠ rootBase}

def pureTranslations (t : HCoordinate → ZMod 7) :
    Set (Equiv.Perm Omega) :=
  {p | p ∈ pointStabilizer t ∧
    ∃ τ : OmegaH → ZMod 7, ∀ x : ZMod 7, ∀ b : OmegaH,
      p (x, b) = (x + τ b, b)}

def fiberProjectionValue (b : OmegaH) (p : Equiv.Perm Omega) : ZMod 7 :=
  (p (0, b)).1

def fiberProjectionNontrivial (t : HCoordinate → ZMod 7)
    (b : OmegaH) : Prop :=
  ∃ p : Equiv.Perm Omega,
    p ∈ pureTranslations t ∧ fiberProjectionValue b p ≠ 0

def fiberProjectionSurjective (t : HCoordinate → ZMod 7)
    (b : OmegaH) : Prop :=
  ∀ y : ZMod 7, ∃ p : Equiv.Perm Omega,
    p ∈ pureTranslations t ∧ fiberProjectionValue b p = y

/-- Claim 28185: the pure-translation part of the actual root stabilizer has
nontrivial, hence surjective, projection on each of the thirty-nine
nonidentity base fibers for every nonzero one-support profile. -/
def rootFixedTranslationSaturation : Prop :=
  ∀ t : HCoordinate → ZMod 7,
    nonzeroNormalizedOneSupport t →
      Set.ncard nonidentityBaseFibers = 39 ∧
        ∀ b : OmegaH, b ∈ nonidentityBaseFibers →
          fiberProjectionNontrivial t b ∧ fiberProjectionSurjective t b

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28185
