import Mathlib
import MathlibPlus.Open.FiberMaps31844
import MathlibPlus.Open.ResearchFormalization.R1119ScalarLift

namespace MathlibPlus.Open.ResearchFormalization.R1119
namespace R29122

abbrev ScalarCarrier29122 (p : ℕ) := ZMod p × S3

def scalarMultiplier29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : (ZMod p)ˣ :=
  ω ^ (e h).val

def scalarValue29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  ((scalarMultiplier29122 ω e h : (ZMod p)ˣ) : ZMod p)

def scalarInverseValue29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : ZMod p :=
  (((scalarMultiplier29122 ω e h)⁻¹ : (ZMod p)ˣ) : ZMod p)

def scalarFiberEquiv29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (e : S3 → ZMod 3) (h : S3) : Equiv.Perm (ZMod p) :=
  Units.mulLeft (scalarMultiplier29122 ω e h)

def scalarLiftEquiv29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Equiv.Perm (ScalarCarrier29122 p) :=
  let toProduct : (Σ _ : S3, ZMod p) ≃ ScalarCarrier29122 p :=
    (Equiv.sigmaEquivProd S3 (ZMod p)).trans (Equiv.prodComm S3 (ZMod p))
  toProduct.symm.trans
    ((Equiv.sigmaCongr σ (fun h => scalarFiberEquiv29122 ω e h)).trans toProduct)

def scalarDerivativeFunction29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (u : ZMod p) (k : S3) : ScalarCarrier29122 p → ScalarCarrier29122 p :=
  let f := scalarLiftEquiv29122 ω σ e
  fun x =>
    f.symm
      (fiberMapProductMul p
        (f (fiberMapProductMul p x (u, k)))
        (fiberMapProductInv p (f (u, k))))

def derivativeSectionStep29122 (σ : Equiv.Perm S3) (h h' : S3) : Prop :=
  ∃ k : S3,
    thetaK σ k h = h' ∨ thetaK σ k h' = h

def derivativeSectionComponent29122 (σ : Equiv.Perm S3) (h₀ : S3) : Set S3 :=
  {h | Relation.ReflTransGen (derivativeSectionStep29122 σ) h₀ h}

def inverseCompatibleSectionComponent29122 (σ : Equiv.Perm S3) (h₀ : S3) : Set S3 :=
  derivativeSectionComponent29122 σ h₀ ∪
    Set.image (fun h : S3 => h⁻¹) (derivativeSectionComponent29122 σ h₀)

def scalarDerivativeStep29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (x y : ScalarCarrier29122 p) : Prop :=
  ∃ (u : ZMod p) (k : S3),
    scalarDerivativeFunction29122 ω σ e u k x = y ∨
      scalarDerivativeFunction29122 ω σ e u k y = x

def scalarDerivativeOrbit29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (x : ScalarCarrier29122 p) : Set (ScalarCarrier29122 p) :=
  {y | Relation.ReflTransGen (scalarDerivativeStep29122 ω σ e) x y}

def scalarMultiplierSubgroup29122 {p : ℕ} (ω : (ZMod p)ˣ) :
    Subgroup (ZMod p)ˣ :=
  Subgroup.closure ({ω} : Set (ZMod p)ˣ)

def multiplierCoset29122 {p : ℕ} (ω : (ZMod p)ˣ) (c : ZMod p) : Set (ZMod p) :=
  {z | ∃ a : scalarMultiplierSubgroup29122 ω,
    z = c * ((a : (ZMod p)ˣ) : ZMod p)}

def inversePairedCosetBlock29122 {p : ℕ} (ω : (ZMod p)ˣ) (c : ZMod p) : Set (ZMod p) :=
  multiplierCoset29122 ω c ∪ multiplierCoset29122 ω (-c)

def fullPrimeSection29122 {p : ℕ} (C : Set S3) : Set (ScalarCarrier29122 p) :=
  {x | x.2 ∈ C}

def zeroPointModel29122 {p : ℕ} (C : Set S3) : Set (ScalarCarrier29122 p) :=
  {x | x.1 = 0 ∧ x.2 ∈ C}

def nonzeroCosetModel29122 {p : ℕ} (ω : (ZMod p)ˣ) (C : Set S3)
    (c : ZMod p) : Set (ScalarCarrier29122 p) :=
  {x | x.2 ∈ C ∧ x.1 ∈ multiplierCoset29122 ω c}

def inverseCompatibleDerivativeBlock29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) (x : ScalarCarrier29122 p) :
    Set (ScalarCarrier29122 p) :=
  scalarDerivativeOrbit29122 ω σ e x ∪
    Set.image (fiberMapProductInv p) (scalarDerivativeOrbit29122 ω σ e x)

def inverseCompatibleDerivativeBlocks29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) :
    Set (Set (ScalarCarrier29122 p)) :=
  {B | ∃ x, B = inverseCompatibleDerivativeBlock29122 ω σ e x}

def productShadow29122 {p : ℕ} (β : S3 ≃* S3) : ScalarCarrier29122 p → ScalarCarrier29122 p :=
  fun x => (x.1, β x.2)

def commonShadowOnModel29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) (β : S3 ≃* S3)
    (M : Set (ScalarCarrier29122 p)) : Prop :=
  Set.image (scalarLiftEquiv29122 ω σ e) M =
    Set.image (productShadow29122 β) M

def commonShadowOnSectionModels29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3) (β : S3 ≃* S3) : Prop :=
  (∀ h₀ : S3,
    let C := derivativeSectionComponent29122 σ h₀
    let Cinv := inverseCompatibleSectionComponent29122 σ h₀
    commonShadowOnModel29122 ω σ e β (fullPrimeSection29122 C) ∧
      commonShadowOnModel29122 ω σ e β (fullPrimeSection29122 Cinv) ∧
      commonShadowOnModel29122 ω σ e β (zeroPointModel29122 Cinv) ∧
      (∀ c : ZMod p, c ≠ 0 →
        commonShadowOnModel29122 ω σ e β
          (nonzeroCosetModel29122 ω Cinv c ∪
            nonzeroCosetModel29122 ω Cinv (-c)))) ∧
  (∀ B ∈ inverseCompatibleDerivativeBlocks29122 ω σ e,
    commonShadowOnModel29122 ω σ e β B)

def p7InversePairedCosetModel29122 : Prop :=
  ∀ (ω : (ZMod 7)ˣ), orderThreeUnit ω →
    Fintype.card (ZMod 7) = 7 ∧
    Fintype.card (ZMod 7)ˣ = 6 ∧
    Fintype.card S3 = 6 ∧
    Fintype.card (ScalarCarrier29122 7) = 42 ∧
    Set.ncard (inversePairedCosetBlock29122 ω 1) = 6 ∧
    (∀ c : ZMod 7, c ≠ 0 →
      inversePairedCosetBlock29122 ω c = inversePairedCosetBlock29122 ω 1) ∧
    (∀ z : ZMod 7, z ≠ 0 →
      z ∈ inversePairedCosetBlock29122 ω 1)

def repeatedNonzeroCosetPairModel29122 (p : ℕ) (ω : (ZMod p)ˣ) : Prop :=
  (∀ c : ZMod p, c ≠ 0 →
    Set.ncard (inversePairedCosetBlock29122 ω c) = 6) ∧
  (∀ z : ZMod p, z ≠ 0 →
    ∃ c : ZMod p, c ≠ 0 ∧ z ∈ inversePairedCosetBlock29122 ω c) ∧
  (∀ c d : ZMod p, c ≠ 0 → d ≠ 0 →
    inversePairedCosetBlock29122 ω c = inversePairedCosetBlock29122 ω d ∨
      Disjoint (inversePairedCosetBlock29122 ω c)
        (inversePairedCosetBlock29122 ω d))

def p7CommonShadowCensus29122 : Prop :=
  ∀ (ω : (ZMod 7)ˣ), orderThreeUnit ω →
    ∀ (σ : Equiv.Perm S3), σ 1 = 1 →
      ∀ (e : S3 → ZMod 3), e 1 = 0 →
        ∃ β : S3 ≃* S3,
          commonShadowOnSectionModels29122 (p := 7) ω σ e β

def identityFree29122 {p : ℕ} (S : Set (ScalarCarrier29122 p)) : Prop :=
  (0, (1 : S3)) ∉ S

def inverseClosed29122 {p : ℕ} (S : Set (ScalarCarrier29122 p)) : Prop :=
  ∀ x, x ∈ S ↔ fiberMapProductInv p x ∈ S

def derivativeInvariant29122 {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (S : Set (ScalarCarrier29122 p)) : Prop :=
  ∀ (u : ZMod p) (k : S3),
    Set.image (scalarDerivativeFunction29122 ω σ e u k) S = S

def allPrimeScalarLiftCollapse29122 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (ω : (ZMod p)ˣ), orderThreeUnit ω →
      ∀ (σ : Equiv.Perm S3), σ 1 = 1 →
        ∀ (e : S3 → ZMod 3), e 1 = 0 →
          ∀ S : Set (ScalarCarrier29122 p),
            identityFree29122 S → inverseClosed29122 S →
              derivativeInvariant29122 ω σ e S →
                ∃ β : S3 ≃* S3,
                  Set.image (scalarLiftEquiv29122 ω σ e) S =
                    Set.image (productShadow29122 β) S

end R29122

/-- Claim 29122: the unique p=7 inverse-paired coset model, its repeated
all-prime version, and one common S3 shadow imply the all-prime collapse. -/
def p7SectionModelIsUniversal : Prop :=
  (R29122.p7InversePairedCosetModel29122 ∧
    (∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
      ∀ (ω : (ZMod p)ˣ), orderThreeUnit ω →
        R29122.repeatedNonzeroCosetPairModel29122 p ω) ∧
    R29122.p7CommonShadowCensus29122) →
      R29122.allPrimeScalarLiftCollapse29122

end MathlibPlus.Open.ResearchFormalization.R1119
