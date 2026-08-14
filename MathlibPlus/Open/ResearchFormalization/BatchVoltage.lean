import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchVoltage

abbrev Three := ZMod 3

def thetaPower {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (i : Three) : M ≃+ M :=
  match i.val with
  | 0 => AddEquiv.refl M
  | 1 => θ
  | _ => θ.trans θ

def semidirectMul {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) : (M × Three) → (M × Three) → (M × Three) :=
  fun a b => (a.1 + thetaPower θ a.2 b.1, a.2 + b.2)

def semidirectInv {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) : (M × Three) → (M × Three) :=
  fun a => (-thetaPower θ (-a.2) a.1, -a.2)

def fixedPointFree {M : Type*} [AddCommGroup M] (θ : M ≃+ M) : Prop :=
  ∀ x, θ x = x → x = 0

def orderThree {M : Type*} [AddCommGroup M] (θ : M ≃+ M) : Prop :=
  θ ≠ AddEquiv.refl M ∧ ∀ x, θ (θ (θ x)) = x

def semidirectCoordinateModel : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Finite M] (θ : M ≃+ M),
    fixedPointFree θ → orderThree θ →
      (∀ a b c,
          semidirectMul θ (semidirectMul θ a b) c =
            semidirectMul θ a (semidirectMul θ b c)) ∧
      (∀ a, semidirectMul θ (0, 0) a = a ∧
        semidirectMul θ a (0, 0) = a ∧
        semidirectMul θ a (semidirectInv θ a) = (0, 0) ∧
        semidirectMul θ (semidirectInv θ a) a = (0, 0))

/-- The order-three norm vanishes on the additive kernel. -/
def orderThreeNormCancellation : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Finite M] (θ : M ≃+ M),
    fixedPointFree θ → orderThree θ →
      ∀ x : M, x + θ x + θ (θ x) = 0

abbrev E (M : Type*) := M × Three

def voltageSlice {M : Type*} (S : Set (E M)) (k : Three) : Set M :=
  {a | (a, k) ∈ S}

def voltageInverseClosed {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set (E M)) : Prop :=
  ∀ x, x ∈ S ↔ semidirectInv θ x ∈ S

def negSet {M : Type*} [AddGroup M] (S : Set M) : Set M :=
  {x | -x ∈ S}

def negThetaImage {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set M) : Set M :=
  {x | ∃ y ∈ S, x = -θ.symm y}

def negThetaTwoImage {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set M) : Set M :=
  {x | ∃ y ∈ S, x = -(thetaPower θ (2 : Three)) y}

/-- The three exact slice equations, including the identity exclusion in the
converse. -/
def inverseClosedVoltageSlices : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Finite M] (θ : M ≃+ M),
    fixedPointFree θ → orderThree θ →
    ∀ S : Set (E M),
      (voltageInverseClosed θ S →
        voltageSlice S 0 = negSet (voltageSlice S 0) ∧
        voltageSlice S 2 = negThetaImage θ (voltageSlice S 1) ∧
        voltageSlice S 2 = negThetaTwoImage θ (voltageSlice S 1)) ∧
      ((0, 0) ∉ S →
        (voltageSlice S 0 = negSet (voltageSlice S 0) ∧
          voltageSlice S 2 = negThetaImage θ (voltageSlice S 1) ∧
          voltageSlice S 2 = negThetaTwoImage θ (voltageSlice S 1)) →
        voltageInverseClosed θ S)

def thetaImage {M : Type*} [AddCommGroup M]
    (θi : M ≃+ M) (S : Set M) : Set M :=
  θi '' S

def voltageAdj {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set (E M)) (x y : E M) : Prop :=
  semidirectMul θ (semidirectInv θ x) y ∈ S

def translationRow {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set (E M)) (i j : Three) (D : Set M) : Prop :=
  ∀ a b, voltageAdj θ S (a, i) (b, j) ↔ b - a ∈ D

/-- Exact labelled rows for the three quotient layers. -/
def threeLayerTranslationRelations : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Finite M] (θ : M ≃+ M),
    fixedPointFree θ → orderThree θ →
    ∀ S : Set (E M), voltageInverseClosed θ S →
      (∀ i : Three,
        translationRow θ S i i
          (thetaImage (thetaPower θ i) (voltageSlice S 0)) ∧
        translationRow θ S i (i + 1)
          (thetaImage (thetaPower θ i) (voltageSlice S 1)) ∧
        translationRow θ S (i + 1) i
          (thetaImage (thetaPower θ (i + 1)) (voltageSlice S 2)))

def complementConnection {M : Type*} [AddCommGroup M] : Set (E M) :=
  {((0 : M), (1 : Three)), ((0 : M), (2 : Three))}

def layer {M : Type*} (i : Three) : Set (E M) :=
  {x | x.2 = i}

def fiber {M : Type*} (a : M) : Set (E M) :=
  {x | x.1 = a}

def graphAutomorphism {M : Type*} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set (E M)) (f : E M ≃ E M) : Prop :=
  ∀ x y, voltageAdj θ S (f x) (f y) ↔ voltageAdj θ S x y

/-- The complement-only branch is a disjoint union of kernel-fibre triangles,
so the characteristic quotient-layer partition is not graph-intrinsic. -/
def complementOnlyLayerObstruction : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Finite M] (θ : M ≃+ M),
    fixedPointFree θ → orderThree θ →
      (∀ a : M, ∀ i j : Three, i ≠ j →
        voltageAdj θ complementConnection (a, i) (a, j)) ∧
      (∀ a b : M, a ≠ b → ∀ i j : Three,
        ¬ voltageAdj θ complementConnection (a, i) (b, j)) ∧
      (letI := Classical.decEq (E M)
       let f : E M ≃ E M :=
         Equiv.swap ((0 : M), (1 : Three)) ((0 : M), (2 : Three))
       graphAutomorphism θ complementConnection f ∧
         f '' layer (1 : Three) ≠ layer (1 : Three))

end MathlibPlus.Open.ResearchFormalization.BatchVoltage
