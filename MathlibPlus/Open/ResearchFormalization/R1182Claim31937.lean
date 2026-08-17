import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31937

open MathlibPlus.Open.Research.Q12PrimeCover

abbrev H := Q12Carrier
abbrev Gp (p : ℕ) := PrimeCoverCarrier p

private def normalizedAffineFunctions (p : ℕ)
    (lam : H → (ZMod p)ˣ) (tau : H → ZMod p) : Prop :=
  lam q12One = 1 ∧ tau q12One = 0

private def relativeDerivative (p : ℕ)
    (lam : H → (ZMod p)ˣ) (tau : H → ZMod p)
    (h : H) (z : Gp p) : Gp p :=
  primeCoverMul p
    (gpAffineLift p lam tau q12Switch
      (primeCoverMul p ((0, h) : Gp p) z))
    (primeCoverInv p
      (gpAffineLift p lam tau q12Switch z))

private def relativeDerivativeFiberAction (p : ℕ)
    (lam : H → (ZMod p)ˣ) (tau : H → ZMod p)
    (h k : H) (x : ZMod p) : ZMod p :=
  (relativeDerivative p lam tau h (x, k)).1

private def varyingCoefficient (p : ℕ)
    (lam : H → (ZMod p)ˣ) (tau : H → ZMod p)
    (h k : H) : ZMod p :=
  relativeDerivativeFiberAction p lam tau h k 1 -
    relativeDerivativeFiberAction p lam tau h k 0

private def scalarProfile (p : ℕ)
    (lam : H → (ZMod p)ˣ) (k : H) : ZMod p :=
  (lam k : ZMod p) * q12Chi p k *
    (q12Chi p (q12Switch k))⁻¹

/-- Claim 31937: the coefficient is extracted from the displayed normalized
relative-derivative action, and its vanishing is exactly left invariance of
the scalar profile. -/
def varyingCoefficientCriterion_claim31937 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : H → (ZMod p)ˣ) (tau : H → ZMod p),
      normalizedAffineFunctions p lam tau →
        (∀ h k : H,
          varyingCoefficient p lam tau h k =
            (lam (q12Mul h k) : ZMod p) * q12Chi p h -
              q12Chi p (q12Switch (q12Mul h k)) *
                (q12Chi p (q12Switch k))⁻¹ * (lam k : ZMod p)) ∧
          (∀ h : H,
            (∀ k : H, varyingCoefficient p lam tau h k = 0) ↔
              ∀ k : H,
                scalarProfile p lam (q12Mul h k) =
                  scalarProfile p lam k)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31937
