import Mathlib
import MathlibPlus.Open.FiberMaps31844
import MathlibPlus.Open.ResearchFormalization.R1119ScalarLift

namespace MathlibPlus.Open.ResearchFormalization.R1119
namespace R29120

abbrev ScalarCarrier29120 (p : ℕ) := ZMod p × S3

def scalarMultiplier29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : (ZMod p)ˣ :=
  ω ^ (e h).val

def scalarValue29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  ((scalarMultiplier29120 ω e h : (ZMod p)ˣ) : ZMod p)

def scalarInverseValue29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  (((scalarMultiplier29120 ω e h)⁻¹ : (ZMod p)ˣ) : ZMod p)

def scalarFiberEquiv29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : Equiv.Perm (ZMod p) :=
  Units.mulLeft (scalarMultiplier29120 ω e h)

def scalarLiftEquiv29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Equiv.Perm (ScalarCarrier29120 p) :=
  let toProduct : (Σ _ : S3, ZMod p) ≃ ScalarCarrier29120 p :=
    (Equiv.sigmaEquivProd S3 (ZMod p)).trans (Equiv.prodComm S3 (ZMod p))
  toProduct.symm.trans
    ((Equiv.sigmaCongr σ (fun h => scalarFiberEquiv29120 ω e h)).trans toProduct)

def translationTerm29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h k : S3) (u : ZMod p) : ZMod p :=
  (scalarValue29120 ω e (h * k) - scalarValue29120 ω e k) * u

def scalarDerivativeFunction29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (u : ZMod p) (k : S3) : ScalarCarrier29120 p → ScalarCarrier29120 p :=
  let f := scalarLiftEquiv29120 ω σ e
  fun x =>
    f.symm
      (fiberMapProductMul p
        (f (fiberMapProductMul p x (u, k)))
        (fiberMapProductInv p (f (u, k))))

def scalarDerivativeFormula29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (u : ZMod p) (k h : S3) (z : ZMod p) : ScalarCarrier29120 p :=
  let θ := thetaK σ k h
  (scalarInverseValue29120 ω e θ *
      (scalarValue29120 ω e (h * k) * z + translationTerm29120 ω e h k u), θ)

def derivativeSectionStep29120 (σ : Equiv.Perm S3) (h h' : S3) : Prop :=
  ∃ k : S3,
    thetaK σ k h = h' ∨ thetaK σ k h' = h

def derivativeSectionComponent29120 (σ : Equiv.Perm S3) (h₀ : S3) : Set S3 :=
  {h | Relation.ReflTransGen (derivativeSectionStep29120 σ) h₀ h}

def scalarDerivativeStep29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (x y : ScalarCarrier29120 p) : Prop :=
  ∃ (u : ZMod p) (k : S3),
    scalarDerivativeFunction29120 ω σ e u k x = y ∨
      scalarDerivativeFunction29120 ω σ e u k y = x

def scalarDerivativeOrbit29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (x : ScalarCarrier29120 p) : Set (ScalarCarrier29120 p) :=
  {y | Relation.ReflTransGen (scalarDerivativeStep29120 ω σ e) x y}

def sectionSaturated29120 {p : ℕ} (O : Set (ScalarCarrier29120 p)) (h : S3) : Prop :=
  ∀ z : ZMod p, (z, h) ∈ O

def translationActive29120 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h k : S3) : Prop :=
  scalarValue29120 ω e (h * k) ≠ scalarValue29120 ω e k

end R29120

/-- Claim 29120: an active affine translation fills the target prime fiber,
and every section in its derivative component is saturated. -/
def translationActiveComponentsSaturatePrimeFibers : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (ω : (ZMod p)ˣ), orderThreeUnit ω →
      ∀ (σ : Equiv.Perm S3), σ 1 = 1 →
        ∀ (e : S3 → ZMod 3), e 1 = 0 →
          ∀ (h₀ h k : S3),
            h ∈ R29120.derivativeSectionComponent29120 σ h₀ →
            R29120.translationActive29120 ω e h k →
              Set.range (R29120.translationTerm29120 ω e h k) = Set.univ ∧
              (∀ z : ZMod p,
                Set.range (fun u : ZMod p =>
                  (R29120.scalarDerivativeFormula29120 ω σ e u k h z).1) =
                  Set.univ) ∧
              (∀ x : R29120.ScalarCarrier29120 p,
                x.2 ∈ R29120.derivativeSectionComponent29120 σ h₀ →
                  R29120.sectionSaturated29120
                    (R29120.scalarDerivativeOrbit29120 ω σ e x) x.2)

end MathlibPlus.Open.ResearchFormalization.R1119
