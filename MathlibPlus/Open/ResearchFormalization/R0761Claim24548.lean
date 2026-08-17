import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0761Claim24548

noncomputable section

private abbrev V := ZMod 3 × ZMod 3

private def eOne : V := (1, 0)
private def eTwo : V := (0, 1)
private def vAnchor : V := eOne + eTwo
private def baseB : Finset V := {0, eOne, eTwo}
private def baseBSet : Set V := (baseB : Set V)
private def baseWSet : Set V := (Set.univ : Set V) \ baseBSet

private abbrev Dih (A : Type*) := A × Bool

private def dihMul {A : Type*} [AddCommGroup A]
    (g h : Dih A) : Dih A :=
  (g.1 + (if g.2 then -h.1 else h.1), Bool.xor g.2 h.2)

private def dihInv {A : Type*} [AddCommGroup A] (g : Dih A) : Dih A :=
  (if g.2 then g.1 else -g.1, g.2)

private def dihOne {A : Type*} [AddCommGroup A] : Dih A := (0, false)

private def layerPreserving {A : Type*} (f : Dih A → Dih A) : Prop :=
  ∀ g, (f g).2 = g.2

private def reflectionAdj {A : Type*} [AddCommGroup A]
    (C : Set A) (g h : Dih A) : Prop :=
  ∃ c ∈ C, h = dihMul (c, true) g

private def baseOrientationReversal (f : Dih V → Dih V) : Prop :=
  Function.Bijective f ∧
    layerPreserving f ∧
      (∀ g, f (dihMul (vAnchor, false) g) =
        dihMul (-vAnchor, false) (f g)) ∧
        (∀ g, f (dihMul (-vAnchor, false) g) =
          dihMul (vAnchor, false) (f g)) ∧
          (∀ g h,
            reflectionAdj baseBSet g h ↔
              reflectionAdj baseBSet (f g) (f h)) ∧
            (∀ g h,
              reflectionAdj baseWSet g h ↔
                reflectionAdj baseWSet (f g) (f h))

private abbrev LiftDih (p : ℕ) := Dih (V × ZMod p)

private def liftRotation (p : ℕ) (a : V) (z : ZMod p) : LiftDih p :=
  ((a, z), false)

private def liftReflection (p : ℕ) (a : V) (z : ZMod p) : LiftDih p :=
  ((a, z), true)

private def liftBLayer (p : ℕ) : Set (LiftDih p) :=
  Set.image (fun b : V => liftReflection p b 0) baseBSet

private def liftWLayer (p : ℕ) : Set (LiftDih p) :=
  Set.image (fun w : V => liftReflection p w 1) baseWSet

private def liftedS (p : ℕ) : Set (LiftDih p) :=
  ({liftRotation p vAnchor 1, liftRotation p (-vAnchor) (-1)} : Set (LiftDih p)) ∪
    liftBLayer p ∪ liftWLayer p

private def liftedT (p : ℕ) : Set (LiftDih p) :=
  ({liftRotation p (-vAnchor) 1, liftRotation p vAnchor (-1)} : Set (LiftDih p)) ∪
    liftBLayer p ∪ liftWLayer p

private def liftMap (f : Dih V → Dih V) (p : ℕ) : LiftDih p → LiftDih p :=
  fun g =>
    (((f (g.1.1, g.2)).1, g.1.2), (f (g.1.1, g.2)).2)

private def cayleyAdj {A : Type*} [AddCommGroup A]
    (S : Set (Dih A)) (g h : Dih A) : Prop :=
  dihMul (dihInv g) h ∈ S

private def liftedGraphIsomorphism (p : ℕ) (f : Dih V → Dih V) : Prop :=
  ∃ e : Equiv.Perm (LiftDih p),
    (∀ g, e g = liftMap f p g) ∧
      ∀ g h,
        cayleyAdj (liftedS p) g h ↔
          cayleyAdj (liftedT p) (e g) (e h)

/-- Claim 24548: the coordinate-preserving lift of the supplied base
orientation reversal is a Cayley graph isomorphism for every prime `p ≥ 5`. -/
def uniformLiftedGraphIsomorphism_claim24548 : Prop :=
  ∃ f : Dih V → Dih V,
    baseOrientationReversal f ∧
      ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
        liftedGraphIsomorphism p f

end

end MathlibPlus.Open.ResearchFormalization.R0761Claim24548
