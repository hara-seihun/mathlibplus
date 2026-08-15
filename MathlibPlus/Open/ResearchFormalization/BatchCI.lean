import Mathlib

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalization.CI

noncomputable section

abbrev W (F : Type) := Fin 2 → F
abbrev B (F : Type) := F × ZMod 3
abbrev G (F : Type) := F × W F × ZMod 3

def omegaPow {F : Type} [Monoid F] (omega : F) (k : ZMod 3) : F :=
  omega ^ k.1

def bMul {F : Type} [Field F] (omega : F) (x y : B F) : B F :=
  (x.1 + omegaPow omega x.2 * y.1, x.2 + y.2)

def gMul {F : Type} [Field F] (omega : F) (x y : G F) : G F :=
  (x.1 + omegaPow omega x.2.2 * y.1,
    x.2.1 + omegaPow omega x.2.2 • y.2.1,
    x.2.2 + y.2.2)

def bInv {F : Type} [Field F] (omega : F) (x : B F) : B F :=
  (-omegaPow omega (-x.2) * x.1, -x.2)

def gInv {F : Type} [Field F] (omega : F) (x : G F) : G F :=
  (-omegaPow omega (-x.2.2) * x.1,
    -omegaPow omega (-x.2.2) • x.2.1,
    -x.2.2)

def qMap {F : Type} [Field F] (h : ZMod 3 → F → W F) (x : G F) : G F :=
  (x.1, x.2.1 + h x.2.2 x.1, x.2.2)

def Dterm {F : Type} [Field F] (omega : F)
    (h : ZMod 3 → F → W F) (s g : B F) : W F :=
  omegaPow omega (-g.2) •
      (h (g.2 + s.2) (g.1 + omegaPow omega g.2 * s.1) - h g.2 g.1) -
    h s.2 s.1

def Hspace {F : Type} [Field F] (omega : F)
    (h : ZMod 3 → F → W F) (s : B F) : Submodule F (W F) :=
  Submodule.span F (Set.range (fun g : B F => Dterm omega h s g))

def Kset {F : Type} [Field F] (omega : F)
    (h : ZMod 3 → F → W F) : Set (B F) :=
  {s | Hspace omega h s = ⊥}

def CayleyRelation {F : Type} [Field F]
    (omega : F) (T : Finset (G F)) (x y : G F) : Prop :=
  gMul omega (gInv omega x) y ∈ T

def CayleyConnected {F : Type} [Field F]
    (omega : F) (T : Finset (G F)) : Prop :=
  ∀ x y : G F,
    x = y ∨ Relation.TransGen (CayleyRelation omega T) x y

def IsRawAutomorphism {F : Type} [Field F]
    (omega : F) (α : G F → G F) : Prop :=
  Function.Bijective α ∧
  (∀ x y, α (gMul omega x y) = gMul omega (α x) (α y)) ∧
  α (0, 0, 0) = (0, 0, 0)

def claim59687 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (omega : ZMod p),
    omega ^ 3 = 1 → omega ≠ 1 →
    ∀ (h : ZMod 3 → ZMod p → W (ZMod p)),
      h 0 0 = 0 →
      ∃ α : G (ZMod p) → G (ZMod p),
        IsRawAutomorphism omega α ∧
        ∀ (S T : Finset (G (ZMod p))),
          (∀ x ∈ T, gInv omega x ∈ T) ∧
          CayleyConnected omega T ∧
          T.card < 2 * p ∧
          (∀ x y, gMul omega (gInv omega x) y ∈ S ↔
            gMul omega (gInv omega (qMap h x)) (qMap h y) ∈ T) →
          (∃ s, s ∈ Kset omega h ∧ s ≠ (0, 0)) ∧
          α '' (S : Set (G (ZMod p))) = (T : Set (G (ZMod p)))

end
end MathlibPlus.Open.ResearchFormalization.CI
