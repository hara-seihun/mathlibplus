import MathlibPlus.Open.ResearchFormalization.ProfileClaims

namespace MathlibPlus.Open.ResearchFormalization.C2CubedC9ComplementClaims

open MathlibPlus.Open.ResearchFormalization.ProfileClaims

abbrev FiberProduct := C2Cubed × C9

/-- The direct-product group operations written on the carrier used by the
identity-base profile. -/
def productIdentity18 : FiberProduct := (0, 1)

def productMul18 (x y : FiberProduct) : FiberProduct :=
  (x.1 + y.1, x.2 * y.2)

def productInv18 (x : FiberProduct) : FiberProduct :=
  (-x.1, x.2⁻¹)

def productDifference18 (x y : FiberProduct) : FiberProduct :=
  productMul18 (productInv18 x) y

def inverseClosed18 (S : Set FiberProduct) : Prop :=
  ∀ ⦃x : FiberProduct⦄, x ∈ S → productInv18 x ∈ S

def connectionSet18 (S : Set FiberProduct) : Prop :=
  productIdentity18 ∉ S ∧ inverseClosed18 S

def ordinaryCayleyAdj18 (S : Set FiberProduct) (x y : FiberProduct) : Prop :=
  x ≠ y ∧ productDifference18 x y ∈ S

def ordinaryGraphIsomorphism18 (S T : Set FiberProduct) : Prop :=
  ∃ e : Equiv.Perm FiberProduct,
    ∀ x y : FiberProduct,
      ordinaryCayleyAdj18 S x y ↔ ordinaryCayleyAdj18 T (e x) (e y)

def identityBaseNormalizedGraphIsomorphism18
    (p : C9 → Equiv.Perm C2Cubed) (S T : Set FiberProduct) : Prop :=
  Set.image (identityBaseProfile p) S = T ∧
    ∀ x y : FiberProduct,
      ordinaryCayleyAdj18 S x y ↔
        ordinaryCayleyAdj18 T (identityBaseProfile p x)
          (identityBaseProfile p y)

def productAutomorphism18 (e : Equiv.Perm FiberProduct) : Prop :=
  e productIdentity18 = productIdentity18 ∧
    ∀ x y : FiberProduct,
      e (productMul18 x y) = productMul18 (e x) (e y)

def automorphismOrbit18 (S T : Set FiberProduct) : Prop :=
  ∃ e : Equiv.Perm FiberProduct,
    productAutomorphism18 e ∧ Set.image e S = T

def exactOrdinaryGraphKey18 {K : Type*}
    (key : Set FiberProduct → K) : Prop :=
  ∀ U V : Set FiberProduct,
    ordinaryGraphIsomorphism18 U V ↔ key U = key V

def ordinaryComplement18 (S : Set FiberProduct) : Set FiberProduct :=
  Set.univ \ ({productIdentity18} ∪ S)

def graphComplementAdj18 (S : Set FiberProduct)
    (x y : FiberProduct) : Prop :=
  x ≠ y ∧ ¬ ordinaryCayleyAdj18 S x y

def atomComplement18 (S : Finset FiberProduct) : Finset FiberProduct :=
  (Finset.univ.erase productIdentity18) \ S

def mapConnection18 (e : Equiv.Perm FiberProduct)
    (S : Finset FiberProduct) : Finset FiberProduct :=
  S.image e

def connectionSetFinset18 (n : ℕ) (S : Finset FiberProduct) : Prop :=
  S.card = n ∧
    S ⊆ (Finset.univ.erase productIdentity18) ∧
      ∀ x : FiberProduct, x ∈ S ↔ productInv18 x ∈ S

def finsetGraphIsomorphism18 (S T : Finset FiberProduct) : Prop :=
  ordinaryGraphIsomorphism18 (S : Set FiberProduct) (T : Set FiberProduct)

def finsetAutomorphismOrbit18 (S T : Finset FiberProduct) : Prop :=
  ∃ e : Equiv.Perm FiberProduct,
    productAutomorphism18 e ∧ mapConnection18 e S = T

/-- Claim 38786: the Record-18 identity-base consequence, its exact
connection-set complement, and the valency-33/38 transfer. -/
def claim_38786 : Prop :=
  (∀ (p : C9 → Equiv.Perm C2Cubed), p 1 = Equiv.refl C2Cubed →
    (∀ S : Set FiberProduct, derivativeInvariant p S →
      Set.image (identityBaseProfile p) S = S) ∧
    (∀ S T : Set FiberProduct,
      connectionSet18 S → connectionSet18 T →
        derivativeInvariant p S →
        identityBaseNormalizedGraphIsomorphism18 p S T →
          automorphismOrbit18 S T ∧
            (∀ {K : Type*} (key : Set FiberProduct → K),
              exactOrdinaryGraphKey18 key → key S = key T)) ∧
    (∀ S : Set FiberProduct,
      Set.image (identityBaseProfile p) S = S →
        Set.image (identityBaseProfile p) (ordinaryComplement18 S) =
          ordinaryComplement18 S)) ∧
  (∀ (e : Equiv.Perm FiberProduct), productAutomorphism18 e →
    ∀ S : Finset FiberProduct,
      mapConnection18 e (atomComplement18 S) =
        atomComplement18 (mapConnection18 e S)) ∧
  (∀ S : Set FiberProduct, connectionSet18 S →
    ∀ x y : FiberProduct,
      ordinaryCayleyAdj18 (ordinaryComplement18 S) x y ↔
        graphComplementAdj18 S x y) ∧
  (∀ S : Finset FiberProduct,
    connectionSetFinset18 33 S →
      connectionSetFinset18 38 (atomComplement18 S)) ∧
  (∀ S T : Finset FiberProduct,
    connectionSetFinset18 33 S → connectionSetFinset18 33 T →
      (finsetGraphIsomorphism18 S T ↔
        finsetGraphIsomorphism18 (atomComplement18 S)
          (atomComplement18 T)) ∧
      (finsetAutomorphismOrbit18 S T ↔
        finsetAutomorphismOrbit18 (atomComplement18 S)
          (atomComplement18 T)))

end MathlibPlus.Open.ResearchFormalization.C2CubedC9ComplementClaims
