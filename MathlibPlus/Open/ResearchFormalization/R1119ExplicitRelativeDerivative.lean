import Mathlib
import MathlibPlus.Open.FiberMaps31844
import MathlibPlus.Open.ResearchFormalization.R1119ScalarLift

namespace MathlibPlus.Open.ResearchFormalization.R1119
namespace R29119

abbrev ScalarCarrier29119 (p : ℕ) := ZMod p × S3

def scalarMultiplier29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : (ZMod p)ˣ :=
  ω ^ (e h).val

def scalarValue29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  ((scalarMultiplier29119 ω e h : (ZMod p)ˣ) : ZMod p)

def scalarInverseValue29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  (((scalarMultiplier29119 ω e h)⁻¹ : (ZMod p)ˣ) : ZMod p)

def scalarFiberEquiv29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : Equiv.Perm (ZMod p) :=
  Units.mulLeft (scalarMultiplier29119 ω e h)

def scalarLiftEquiv29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Equiv.Perm (ScalarCarrier29119 p) :=
  let toProduct : (Σ _ : S3, ZMod p) ≃ ScalarCarrier29119 p :=
    (Equiv.sigmaEquivProd S3 (ZMod p)).trans (Equiv.prodComm S3 (ZMod p))
  toProduct.symm.trans
    ((Equiv.sigmaCongr σ (fun h => scalarFiberEquiv29119 ω e h)).trans toProduct)

def translationTerm29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h k : S3) (u : ZMod p) : ZMod p :=
  (scalarValue29119 ω e (h * k) - scalarValue29119 ω e k) * u

def scalarDerivativeFunction29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (u : ZMod p) (k : S3) : ScalarCarrier29119 p → ScalarCarrier29119 p :=
  let f := scalarLiftEquiv29119 ω σ e
  fun x =>
    f.symm
      (fiberMapProductMul p
        (f (fiberMapProductMul p x (u, k)))
        (fiberMapProductInv p (f (u, k))))

def scalarDerivativeFormula29119 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (u : ZMod p) (k h : S3) (z : ZMod p) : ScalarCarrier29119 p :=
  let θ := thetaK σ k h
  (scalarInverseValue29119 ω e θ *
      (scalarValue29119 ω e (h * k) * z + translationTerm29119 ω e h k u), θ)

end R29119

/-- Claim 29119: the normalized relative derivative has the displayed
section transition and affine prime-coordinate formula. -/
def explicitRelativeDerivativeFormula : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (ω : (ZMod p)ˣ), orderThreeUnit ω →
      ∀ (σ : Equiv.Perm S3), σ 1 = 1 →
        ∀ (e : S3 → ZMod 3), e 1 = 0 →
          ∀ (u : ZMod p) (k : S3),
            (∀ (z : ZMod p) (h : S3),
              R29119.scalarDerivativeFunction29119 ω σ e u k (z, h) =
                R29119.scalarDerivativeFormula29119 ω σ e u k h z) ∧
            (∀ h : S3,
              Set.image (R29119.scalarDerivativeFunction29119 ω σ e u k)
                  (fiberMapSection p h) =
                fiberMapSection p (thetaK σ k h))

end MathlibPlus.Open.ResearchFormalization.R1119
