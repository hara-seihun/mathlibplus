import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31936

open MathlibPlus.Open.Research.Q12PrimeCover

abbrev H := Q12Carrier
abbrev Gp (p : ℕ) := PrimeCoverCarrier p

private def normalizedAffineFunctions (p : ℕ)
    (lam : H → (ZMod p)ˣ) (tau : H → ZMod p) : Prop :=
  lam q12One = 1 ∧ tau q12One = 0

private def gpSemidirectGroupLaws (p : ℕ) : Prop :=
  (∀ x y z : Gp p,
      primeCoverMul p (primeCoverMul p x y) z =
        primeCoverMul p x (primeCoverMul p y z)) ∧
    (∀ x : Gp p,
      primeCoverMul p (primeCoverOne p) x = x ∧
        primeCoverMul p x (primeCoverOne p) = x) ∧
    (∀ x : Gp p,
      primeCoverMul p (primeCoverInv p x) x = primeCoverOne p ∧
        primeCoverMul p x (primeCoverInv p x) = primeCoverOne p)

private def gpQuaternionCorrespondence (p : ℕ) : Prop :=
  ∃ e : Gp p → QuaternionGroup (3 * p),
    Function.Bijective e ∧
      e (primeCoverOne p) = 1 ∧
      (∀ x y : Gp p,
        e (primeCoverMul p x y) = e x * e y) ∧
      (∀ x : Gp p,
        e (primeCoverInv p x) = (e x)⁻¹)

private def normalizedAffineLift (p : ℕ)
    (f : Gp p → Gp p) : Prop :=
  Function.Bijective f ∧
    f (primeCoverOne p) = primeCoverOne p ∧
    (∀ x : ZMod p, ∀ h : H,
      (f (x, h)).2 = q12Switch h) ∧
    (∀ h : H, ∃ u : (ZMod p)ˣ, ∃ v : ZMod p,
      (∀ x : ZMod p,
        (f (x, h)).1 = (u : ZMod p) * x + v) ∧
      (h = q12One → u = 1 ∧ v = 0))

/-- Claim 31936: the prime-block semidirect carrier, its generalized
quaternion identification, and the exact unit-slope normalized affine-lift
form over the fixed exceptional quotient switch. -/
def normalizedAffinePrimeBlockLift_claim31936 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    gpSemidirectGroupLaws p ∧
      gpQuaternionCorrespondence p ∧
      (∀ (lam : H → (ZMod p)ˣ) (tau : H → ZMod p),
        normalizedAffineFunctions p lam tau →
          Function.Bijective
            (gpAffineLift p lam tau q12Switch) ∧
            normalizedAffineLift p (gpAffineLift p lam tau q12Switch) ∧
            (∀ x : ZMod p, ∀ h : H,
              gpAffineLift p lam tau q12Switch (x, h) =
                ((lam h : ZMod p) * x + tau h, q12Switch h))) ∧
      (∀ f : Gp p → Gp p,
        normalizedAffineLift p f →
          ∃ (lam : H → (ZMod p)ˣ) (tau : H → ZMod p),
            normalizedAffineFunctions p lam tau ∧
              f = gpAffineLift p lam tau q12Switch)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31936
