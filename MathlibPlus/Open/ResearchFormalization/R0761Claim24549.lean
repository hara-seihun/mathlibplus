import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0761Claim24549

noncomputable section

private abbrev V := ZMod 3 × ZMod 3

private abbrev Dih (A : Type*) := A × Bool

private def dihMul {A : Type*} [AddCommGroup A]
    (g h : Dih A) : Dih A :=
  (g.1 + (if g.2 then -h.1 else h.1), Bool.xor g.2 h.2)

private def dihOne {A : Type*} [AddCommGroup A] : Dih A := (0, false)

private def isDihAutomorphism {A : Type*} [AddCommGroup A]
    (φ : Dih A ≃ Dih A) : Prop :=
  φ (dihOne : Dih A) = dihOne ∧
    ∀ g h, φ (dihMul g h) = dihMul (φ g) (φ h)

private abbrev LiftDih (p : ℕ) := Dih (V × ZMod p)

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

/-- Claim 24549: every automorphism of the odd-prime lifted generalized
-dihedral group has the stated affine form on its rotation kernel and
-reflection coset. -/
def affineNormalFormOddLiftedAutomorphisms_claim24549 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    ∀ (φ : LiftDih p ≃ LiftDih p),
      isDihAutomorphism φ →
      ∃ P : AffineParameters p, affineForm φ P

end

end MathlibPlus.Open.ResearchFormalization.R0761Claim24549
