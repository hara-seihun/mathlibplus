import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.LiftedSetsExact

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

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

private def dihRot {A : Type*} [AddCommGroup A] (a : A) : Dih A := (a, false)

private def dihRefl {A : Type*} [AddCommGroup A] (a : A) : Dih A := (a, true)

private abbrev LiftDih (p : ℕ) := Dih (V × ZMod p)

private def liftRotation (p : ℕ) (a : V) (z : ZMod p) : LiftDih p :=
  dihRot (a, z)

private def liftReflection (p : ℕ) (a : V) (z : ZMod p) : LiftDih p :=
  dihRefl (a, z)

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

private def inverseClosed (S : Set (LiftDih p)) : Prop :=
  ∀ g, g ∈ S ↔ dihInv g ∈ S

private def identityFree (S : Set (LiftDih p)) : Prop :=
  dihOne ∉ S

/-- The concrete cyclic-voltage lifts are inverse-closed, identity-free, and
have the displayed valency eleven for every prime p at least five. -/
def claim24547 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    inverseClosed (liftedS p) ∧
      inverseClosed (liftedT p) ∧
      identityFree (liftedS p) ∧
      identityFree (liftedT p) ∧
      Set.ncard (liftedS p) = 11 ∧
      Set.ncard (liftedT p) = 11

end
end MathlibPlus.Open.Research.LiftedSetsExact
