import Mathlib
import MathlibPlus.Open.FiberMaps31844
import MathlibPlus.Open.ResearchFormalization.R1119ScalarLift

namespace MathlibPlus.Open.ResearchFormalization.R1119
namespace R29121

abbrev ScalarCarrier29121 (p : ℕ) := ZMod p × S3

def scalarMultiplier29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : (ZMod p)ˣ :=
  ω ^ (e h).val

def scalarValue29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  ((scalarMultiplier29121 ω e h : (ZMod p)ˣ) : ZMod p)

def scalarInverseValue29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  (((scalarMultiplier29121 ω e h)⁻¹ : (ZMod p)ˣ) : ZMod p)

def scalarFiberEquiv29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : Equiv.Perm (ZMod p) :=
  Units.mulLeft (scalarMultiplier29121 ω e h)

def scalarLiftEquiv29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Equiv.Perm (ScalarCarrier29121 p) :=
  let toProduct : (Σ _ : S3, ZMod p) ≃ ScalarCarrier29121 p :=
    (Equiv.sigmaEquivProd S3 (ZMod p)).trans (Equiv.prodComm S3 (ZMod p))
  toProduct.symm.trans
    ((Equiv.sigmaCongr σ (fun h => scalarFiberEquiv29121 ω e h)).trans toProduct)

def translationTerm29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h k : S3) (u : ZMod p) : ZMod p :=
  (scalarValue29121 ω e (h * k) - scalarValue29121 ω e k) * u

def scalarDerivativeFunction29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (u : ZMod p) (k : S3) : ScalarCarrier29121 p → ScalarCarrier29121 p :=
  let f := scalarLiftEquiv29121 ω σ e
  fun x =>
    f.symm
      (fiberMapProductMul p
        (f (fiberMapProductMul p x (u, k)))
        (fiberMapProductInv p (f (u, k))))

def derivativeSectionStep29121 (σ : Equiv.Perm S3) (h h' : S3) : Prop :=
  ∃ k : S3,
    thetaK σ k h = h' ∨ thetaK σ k h' = h

def derivativeSectionComponent29121 (σ : Equiv.Perm S3) (h₀ : S3) : Set S3 :=
  {h | Relation.ReflTransGen (derivativeSectionStep29121 σ) h₀ h}

def inverseCompatibleSectionComponent29121 (σ : Equiv.Perm S3) (h₀ : S3) : Set S3 :=
  derivativeSectionComponent29121 σ h₀ ∪
    Set.image (fun h : S3 => h⁻¹) (derivativeSectionComponent29121 σ h₀)

def scalarDerivativeStep29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (x y : ScalarCarrier29121 p) : Prop :=
  ∃ (u : ZMod p) (k : S3),
    scalarDerivativeFunction29121 ω σ e u k x = y ∨
      scalarDerivativeFunction29121 ω σ e u k y = x

def scalarDerivativeOrbit29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (x : ScalarCarrier29121 p) : Set (ScalarCarrier29121 p) :=
  {y | Relation.ReflTransGen (scalarDerivativeStep29121 ω σ e) x y}

def scalarMultiplierSubgroup29121 {p : ℕ} (ω : (ZMod p)ˣ) :
    Subgroup (ZMod p)ˣ :=
  Subgroup.closure ({ω} : Set (ZMod p)ˣ)

def multiplierCoset29121 {p : ℕ} (ω : (ZMod p)ˣ) (c : ZMod p) : Set (ZMod p) :=
  {z | ∃ a : scalarMultiplierSubgroup29121 ω,
    z = c * ((a : (ZMod p)ˣ) : ZMod p)}

def inversePairedCosetBlock29121 {p : ℕ} (ω : (ZMod p)ˣ) (c : ZMod p) : Set (ZMod p) :=
  multiplierCoset29121 ω c ∪ multiplierCoset29121 ω (-c)

def zeroPointModel29121 {p : ℕ} (C : Set S3) : Set (ScalarCarrier29121 p) :=
  {x | x.1 = 0 ∧ x.2 ∈ C}

def nonzeroCosetModel29121 {p : ℕ} (ω : (ZMod p)ˣ) (C : Set S3)
    (c : ZMod p) : Set (ScalarCarrier29121 p) :=
  {x | x.2 ∈ C ∧ x.1 ∈ multiplierCoset29121 ω c}

def scalarDerivativeMultiplier29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) (h k : S3) : (ZMod p)ˣ :=
  (scalarMultiplier29121 ω e (thetaK σ k h))⁻¹ * scalarMultiplier29121 ω e (h * k)

def translationQuietOnComponent29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) (h₀ : S3) : Prop :=
  ∀ h ∈ derivativeSectionComponent29121 σ h₀, ∀ k : S3,
    scalarValue29121 ω e (h * k) = scalarValue29121 ω e k

def inverseCompatibleDerivativeBlock29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) (x : ScalarCarrier29121 p) :
    Set (ScalarCarrier29121 p) :=
  scalarDerivativeOrbit29121 ω σ e x ∪
    Set.image (fiberMapProductInv p) (scalarDerivativeOrbit29121 ω σ e x)

def inverseCompatibleDerivativeBlocks29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Set (Set (ScalarCarrier29121 p)) :=
  {B | ∃ x, B = inverseCompatibleDerivativeBlock29121 ω σ e x}

def inverseCompatibleQuietDerivativeBlocks29121 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Set (Set (ScalarCarrier29121 p)) :=
  {B | ∃ h₀ : S3,
      translationQuietOnComponent29121 ω σ e h₀ ∧
      ∃ x : ScalarCarrier29121 p,
        x.2 ∈ derivativeSectionComponent29121 σ h₀ ∧
        B = inverseCompatibleDerivativeBlock29121 ω σ e x}

end R29121

/-- Claim 29121: in a translation-quiet section component, the actual
inverse-compatible derivative blocks are the separate zero model or the
paired nonzero multiplier-coset models. -/
def quietComponentsAreInversePairedMultiplierCosets : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (ω : (ZMod p)ˣ), orderThreeUnit ω →
      ∀ (σ : Equiv.Perm S3), σ 1 = 1 →
        ∀ (e : S3 → ZMod 3), e 1 = 0 →
          (∀ (h₀ : S3),
            R29121.translationQuietOnComponent29121 ω σ e h₀ →
              let C := R29121.derivativeSectionComponent29121 σ h₀
              let Cinv := R29121.inverseCompatibleSectionComponent29121 σ h₀
              (∀ h ∈ C, ∀ k : S3,
                R29121.scalarDerivativeMultiplier29121 ω σ e h k ∈
                  R29121.scalarMultiplierSubgroup29121 ω) ∧
              (∀ h ∈ C, ∀ (u : ZMod p) (k : S3),
                R29121.scalarDerivativeFunction29121 ω σ e u k (0, h) ∈
                  R29121.zeroPointModel29121 Cinv) ∧
              Disjoint (R29121.zeroPointModel29121 Cinv)
                {x : R29121.ScalarCarrier29121 p | x.1 ≠ 0} ∧
              (∀ z : ZMod p, z ≠ 0 →
                ∃ c : ZMod p, c ≠ 0 ∧
                  z ∈ R29121.multiplierCoset29121 ω c) ∧
              (∀ c d : ZMod p, c ≠ 0 → d ≠ 0 →
                R29121.multiplierCoset29121 ω c =
                    R29121.multiplierCoset29121 ω d ∨
                  Disjoint (R29121.multiplierCoset29121 ω c)
                    (R29121.multiplierCoset29121 ω d)) ∧
              (∀ c : ZMod p, c ≠ 0 → ∀ h ∈ C,
                ∀ (u : ZMod p) (k : S3) (z : ZMod p),
                  z ∈ R29121.multiplierCoset29121 ω c →
                    (R29121.scalarDerivativeFunction29121 ω σ e u k (z, h)).1 ∈
                      R29121.multiplierCoset29121 ω c) ∧
              (∀ c : ZMod p, c ≠ 0 →
                Set.image (fun z : ZMod p => -z)
                    (R29121.multiplierCoset29121 ω c) =
                  R29121.multiplierCoset29121 ω (-c))) ∧
          (∀ B ∈ R29121.inverseCompatibleQuietDerivativeBlocks29121 ω σ e,
            ∃ (h₀ : S3) (x : R29121.ScalarCarrier29121 p),
              R29121.translationQuietOnComponent29121 ω σ e h₀ ∧
              x.2 ∈ R29121.derivativeSectionComponent29121 σ h₀ ∧
              B = R29121.inverseCompatibleDerivativeBlock29121 ω σ e x ∧
              ((x.1 = 0 ∧
                  B = R29121.zeroPointModel29121
                    (R29121.inverseCompatibleSectionComponent29121 σ h₀)) ∨
                (x.1 ≠ 0 ∧
                  ∃ c : ZMod p, c ≠ 0 ∧
                    B =
                      (R29121.nonzeroCosetModel29121 ω
                        (R29121.inverseCompatibleSectionComponent29121 σ h₀) c ∪
                       R29121.nonzeroCosetModel29121 ω
                        (R29121.inverseCompatibleSectionComponent29121 σ h₀) (-c)))))

end MathlibPlus.Open.ResearchFormalization.R1119
