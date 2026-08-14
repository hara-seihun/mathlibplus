import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

abbrev ShearF11 := ZMod 11

structure ShearQ where
  y : ZMod 5
  i : Fin 4
  deriving DecidableEq, Fintype

def shearQOne : ShearQ := ⟨0, ⟨0, by omega⟩⟩

def shearQMul (a b : ShearQ) : ShearQ :=
  let even : Prop := a.i.1 % 2 = 0
  let e : ZMod 5 := if even then 1 else -1
  ⟨a.y + e * b.y, ⟨(a.i.1 + b.i.1) % 4, by omega⟩⟩

def shearQInv (a : ShearQ) : ShearQ :=
  let even : Prop := a.i.1 % 2 = 0
  let e : ZMod 5 := if even then 1 else -1
  ⟨-(e * a.y), ⟨(4 - a.i.1) % 4, by omega⟩⟩

def shearChi (q : ShearQ) : ShearF11 :=
  if q.i.1 % 2 = 0 then 1 else -1

def normalizedShearProfile (φ : ShearQ → ShearF11) : Prop :=
  φ shearQOne = 0

def triangularShear (φ : ShearQ → ShearF11)
    (x : ShearF11) (q : ShearQ) : ShearF11 × ShearQ :=
  (x + φ q, q)

def verticalShear (f : ShearQ → ShearF11)
    (x : ShearF11) (q : ShearQ) : ShearF11 × ShearQ :=
  (x + f q, q)

def shearDifference (φ : ShearQ → ShearF11)
    (h r : ShearQ) : ShearF11 :=
  φ r - φ (shearQMul r (shearQInv h))

def shearRightTranslate (u : ShearQ)
    (f : ShearQ → ShearF11) : ShearQ → ShearF11 :=
  fun r => f (shearQMul r (shearQInv u))

def shearDifferenceModule (φ : ShearQ → ShearF11) :
    Submodule ShearF11 (ShearQ → ShearF11) :=
  Submodule.span ShearF11
    {f | ∃ h u : ShearQ,
      f = shearRightTranslate u (shearDifference φ h)}

def shearLambda (q : ShearQ) (f : ShearQ → ShearF11) : ShearF11 :=
  f q - shearChi q * f shearQOne

def shearDefectSet (φ : ShearQ → ShearF11) : Set ShearQ :=
  {q | q ≠ shearQOne ∧
    ∀ f, f ∈ shearDifferenceModule φ → shearLambda q f = 0}

def shearPow (a : ShearQ) : ℕ → ShearQ
  | 0 => shearQOne
  | k + 1 => shearQMul (shearPow a k) a

def shearExactOrder (a : ShearQ) (k : ℕ) : Prop :=
  shearPow a k = shearQOne ∧
    ∀ j : ℕ, 0 < j → j < k → shearPow a j ≠ shearQOne

def quotientSupport (φ : ShearQ → ShearF11) : ℕ :=
  Fintype.card {q : ShearQ // φ q ≠ 0}

/-- Claim 43664: the normalized profile and both axis-aligned shears are the
literal maps on the fixed `C₅ ⋊ C₄` quotient. -/
def normalizedAxisAlignedShears : Prop :=
  ∀ φ : ShearQ → ShearF11,
    normalizedShearProfile φ →
    (∀ x q, triangularShear φ x q = (x + φ q, q)) ∧
    (∀ f x q, verticalShear f x q = (x + f q, q))

/-- Claim 43670: the exact defect identity and the order shape of a nonzero
defect for the displayed operation. -/
def nonzeroDefectShape : Prop :=
  ∀ φ : ShearQ → ShearF11,
    normalizedShearProfile φ →
    ∀ h : ShearQ, h ∈ shearDefectSet φ →
      let a := φ h
      (∀ q : ShearQ,
        φ (shearQMul h q) = shearChi h * φ q + a) ∧
      (shearChi h = 1 → shearPow h 10 = shearQOne) ∧
      (a ≠ 0 → shearChi h = -1 ∧ shearExactOrder h 4)

/-- Claim 43671: every genuine nonzero defect has quotient support at least
10, with support counted on the 20 quotient points. -/
def genuineDefectSupportBound : Prop :=
  ∀ φ : ShearQ → ShearF11,
    normalizedShearProfile φ →
    ∀ h : ShearQ, h ∈ shearDefectSet φ → φ h ≠ 0 →
      quotientSupport φ ≥ 10

end

end MathlibPlus.Open.GraphTheory
