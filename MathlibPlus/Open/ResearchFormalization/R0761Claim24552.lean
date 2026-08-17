import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0761Claim24552

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

private def dihRot {A : Type*} [AddCommGroup A] (a : A) : Dih A := (a, false)

private def dihRefl {A : Type*} [AddCommGroup A] (a : A) : Dih A := (a, true)

private def isDihAutomorphism {A : Type*} [AddCommGroup A]
    (φ : Dih A ≃ Dih A) : Prop :=
  φ (dihOne : Dih A) = dihOne ∧
    ∀ g h, φ (dihMul g h) = dihMul (φ g) (φ h)

private def mapsConnectionSet {A : Type*} [AddCommGroup A]
    (φ : Dih A ≃ Dih A) (S T : Set (Dih A)) : Prop :=
  ∀ g, g ∈ S ↔ φ g ∈ T

private def inverseClosed {A : Type*} [AddCommGroup A]
    (S : Set (Dih A)) : Prop :=
  ∀ g, g ∈ S ↔ dihInv g ∈ S

private def identityFree {A : Type*} [AddCommGroup A]
    (S : Set (Dih A)) : Prop :=
  dihOne ∉ S

private def cayleyAdjacency {A : Type*} [AddCommGroup A]
    (S : Set (Dih A)) (g h : Dih A) : Prop :=
  dihMul (dihInv g) h ∈ S

private def cayleyGraphIsomorphism {A : Type*} [AddCommGroup A]
    (S T : Set (Dih A)) : Prop :=
  ∃ e : Equiv.Perm (Dih A),
    ∀ g h, cayleyAdjacency S g h ↔ cayleyAdjacency T (e g) (e h)

private def undirectedCIGroup {A : Type*} [AddCommGroup A] : Prop :=
  ∀ S T : Set (Dih A),
    inverseClosed S → identityFree S →
    inverseClosed T → identityFree T →
    cayleyGraphIsomorphism S T →
    ∃ φ : Dih A ≃ Dih A,
      isDihAutomorphism φ ∧ mapsConnectionSet φ S T

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

private structure AffineParameters (p : ℕ) where
  M : V ≃+ V
  u : (ZMod p)ˣ
  tV : V
  tP : ZMod p

private def affineMap {p : ℕ} (P : AffineParameters p) : LiftDih p → LiftDih p :=
  fun g =>
    ((P.M g.1.1 + if g.2 then P.tV else 0,
      (P.u : ZMod p) * g.1.2 + if g.2 then P.tP else 0), g.2)

private def affineForm {p : ℕ}
    (φ : LiftDih p ≃ LiftDih p) (P : AffineParameters p) : Prop :=
  ∀ g, φ g = affineMap P g

private def affineKernelMap (P : AffineParameters p) (a : V) : V :=
  P.M a + P.tV

private def exactlyOne (P Q : Prop) : Prop :=
  (P ∧ ¬ Q) ∨ (Q ∧ ¬ P)

/-- Claim 24552. -/
def claim24552 : Prop :=
  (∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    ∀ (φ : LiftDih p ≃ LiftDih p) (P : AffineParameters p),
      isDihAutomorphism φ → affineForm φ P →
      mapsConnectionSet φ (liftedS p) (liftedT p) →
      P.u = -1 → P.M vAnchor = vAnchor →
      P.tP = 1 ∧
        Set.image φ (liftBLayer p) = liftWLayer p ∧
        Set.ncard (liftBLayer p) = 3 ∧
        Set.ncard (liftWLayer p) = 6) ∧
  (∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    ¬ ∃ (φ : LiftDih p ≃ LiftDih p) (P : AffineParameters p),
      isDihAutomorphism φ ∧ affineForm φ P ∧
      mapsConnectionSet φ (liftedS p) (liftedT p) ∧
      P.u = -1 ∧ P.M vAnchor = vAnchor)


end

end MathlibPlus.Open.ResearchFormalization.R0761Claim24552
