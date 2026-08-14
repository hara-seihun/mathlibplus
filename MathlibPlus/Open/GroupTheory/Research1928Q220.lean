import Mathlib

namespace MathlibPlus.Open.GroupTheory.Research1928

structure Q220 where
  x : ZMod 11
  y : ZMod 5
  i : ZMod 4
  deriving DecidableEq, Fintype

def q220Odd (i : ZMod 4) : Prop := ZMod.val i % 2 = 1

def q220Mul (a b : Q220) : Q220 :=
  { x := a.x + (if ZMod.val a.i % 2 = 1 then -b.x else b.x)
    y := a.y + (if ZMod.val a.i % 2 = 1 then -b.y else b.y)
    i := a.i + b.i }

def q220Automorphism (f : Q220 → Q220) : Prop :=
  Function.Bijective f ∧ ∀ a b : Q220, f (q220Mul a b) = q220Mul (f a) (f b)

def q220Profile : Type := (ZMod 5 × ZMod 4) → ZMod 11

def normalizedQ220Profile (φ : q220Profile) : Prop := φ (0, 0) = 0

noncomputable def q220ProfileSupport (φ : q220Profile) : Finset (ZMod 5 × ZMod 4) := by
  classical
  exact Finset.univ.filter (fun yi => φ yi ≠ 0)

def q220AxisSupportTwo (φ : q220Profile) : Prop :=
  normalizedQ220Profile φ ∧ (q220ProfileSupport φ).card = 2

def q220Unit11 (u : Fin 10) : ZMod 11 := (u.1 + 1 : ℕ)
def q220Unit5 (v : Fin 4) : ZMod 5 := (v.1 + 1 : ℕ)

def q220Epsilon (e : Fin 2) : ZMod 4 := if e = 0 then 1 else 3

structure Q220Param where
  u : Fin 10
  v : Fin 4
  s : ZMod 11
  t : ZMod 5
  ε : Fin 2
  deriving DecidableEq, Fintype

def q220ParamMap (p : Q220Param) (g : Q220) : Q220 :=
  { x := q220Unit11 p.u * g.x + if ZMod.val g.i % 2 = 1 then p.s else 0
    y := q220Unit5 p.v * g.y + if ZMod.val g.i % 2 = 1 then p.t else 0
    i := q220Epsilon p.ε * g.i }

def q220Shear (φ : q220Profile) (g : Q220) : Q220 :=
  { x := g.x + φ (g.y, g.i), y := g.y, i := g.i }

def q220ProfileAction (p : Q220Param) (φ : q220Profile)
    (y : ZMod 5) (i : ZMod 4) : ZMod 11 :=
  q220Unit11 p.u *
    φ ((q220Unit5 p.v)⁻¹ * (y - if ZMod.val i % 2 = 1 then p.t else 0),
      q220Epsilon p.ε * i)

def sameQ220ProfileParametersExceptS (p p' : Q220Param) : Prop :=
  p.u = p'.u ∧ p.v = p'.v ∧ p.t = p'.t ∧ p.ε = p'.ε

/-- Claim 36243: the exact 4,400-element parameter family is the complete
identity-fixing aligned-grid normalizer, and its induced profile action is the
displayed formula. -/
def exactQ220NormalizerAndProfileAction_claim36243 : Prop :=
  (10 : ℕ) * 4 * 11 * 5 * 2 = 4400 ∧
  (∀ p : Q220Param, q220Automorphism (q220ParamMap p)) ∧
  (∀ f : Q220 → Q220, q220Automorphism f →
    ∃! p : Q220Param, ∀ g : Q220, f g = q220ParamMap p g) ∧
  (∀ p : Q220Param, ∀ φ : q220Profile, ∀ g : Q220,
    q220ParamMap p (q220Shear φ g) =
      q220Shear (fun yi => q220ProfileAction p φ yi.1 yi.2)
        (q220ParamMap p g)) ∧
  (∀ p p' : Q220Param, sameQ220ProfileParametersExceptS p p' →
    ∀ φ : q220Profile, ∀ y : ZMod 5, ∀ i : ZMod 4,
      q220ProfileAction p φ y i = q220ProfileAction p' φ y i) ∧
  (∃ p : Q220Param, p.s = 0 ∧ p.t = 0 ∧
    ∀ φ y i, q220ProfileAction p φ y i =
      q220Unit11 p.u *
        φ ((q220Unit5 p.v)⁻¹ * y, q220Epsilon p.ε * i))

end MathlibPlus.Open.GroupTheory.Research1928
