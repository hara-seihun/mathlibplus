import Mathlib

noncomputable section
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace MathlibPlus
namespace Open
namespace ResearchFormalizationBatch

/-! The following declarations retain the carriers and quantifiers in the
    admitted claims.  The declarations marked by claim number are open
    propositions; the surrounding definitions only name the carriers and
    operations used by those propositions. -/

namespace R0966

/-- The multiplication formula for the `A ⋊ C₃` carrier in Claim 27690. -/
def semidirectProductMul {A : Type*} [AddCommGroup A]
    (theta : A ≃+ A) (x y : A × ZMod 3) : A × ZMod 3 :=
  (x.1 + (theta : A → A)^[x.2.val] y.1, x.2 + y.2)

/-- Claim 27690. -/
def fixedPointFreeOrderThreeSemidirectProduct
    (A : Type*) [AddCommGroup A] [Fintype A] (theta : A ≃+ A) : Prop :=
  (theta : A → A)^[3] = id ∧
    theta ≠ AddEquiv.refl A ∧
    (∀ a : A, theta a = a → a = 0) ∧
    (∀ (a b : A) (i j : ZMod 3),
      semidirectProductMul theta (a, i) (b, j) =
        (a + (theta : A → A)^[i.val] b, i + j))

/-- Claim 27691.  The quotient coordinate is the `C₃` coordinate on the
    displayed semidirect-product carrier. -/
def normalizedQuotientIdentityFiberProfile
    (A : Type*) [AddCommGroup A] [Fintype A] (theta : A ≃+ A)
    (f : (A × ZMod 3) → (A × ZMod 3)) : Prop :=
  fixedPointFreeOrderThreeSemidirectProduct A theta →
    ((Function.Bijective f ∧
        (∀ (a : A) (i : ZMod 3), (f (a, i)).2 = i) ∧
        (∀ a : A, f (a, 0) = (a, 0))) ↔
      ∃ (phi0 phi1 phi2 : Equiv.Perm A),
        phi0 = Equiv.refl A ∧
        ∀ a : A,
          f (a, 0) = (phi0 a, 0) ∧
          f (a, 1) = (phi1 a, 1) ∧
          f (a, 2) = (phi2 a, 2))

/-- The coordinate correction used in Claim 27697. -/
def complementCoboundaryShift {A : Type*} [AddCommGroup A]
    (theta : A ≃+ A) (c : A) (i : ZMod 3) : A :=
  if i = 0 then 0 else if i = 1 then c else c + theta c

def complementCoboundaryMap {A : Type*} [AddCommGroup A]
    (theta : A ≃+ A) (c : A) (x : A × ZMod 3) : A × ZMod 3 :=
  (x.1 + complementCoboundaryShift theta c x.2, x.2)

/-- Claim 27697. -/
def complementCoboundaryAutomorphism
    (A : Type*) [AddCommGroup A] [Fintype A] (theta : A ≃+ A) : Prop :=
  fixedPointFreeOrderThreeSemidirectProduct A theta →
    ∀ c : A,
      Function.Bijective (complementCoboundaryMap theta c) ∧
        ∀ x y : A × ZMod 3,
          complementCoboundaryMap theta c
              (semidirectProductMul theta x y) =
            semidirectProductMul theta
              (complementCoboundaryMap theta c x)
              (complementCoboundaryMap theta c y)

end R0966

namespace R1307

/-- `P = A^X` with `A = C_m`, represented by `ZMod m`. -/
def coordinateProjection (m : ℕ) [NeZero m] {X : Type*} [Fintype X]
    (x : X) : (X → ZMod m) →+ ZMod m :=
  Pi.evalAddMonoidHom (fun _ : X => ZMod m) x

def coordinateProjectionOnM (m : ℕ) [NeZero m] {X : Type*} [Fintype X]
    (M : AddSubgroup (X → ZMod m)) (x : X) : M →+ ZMod m :=
  (coordinateProjection m x).comp M.subtype

def coordinateKernel (m : ℕ) [NeZero m] {X : Type*} [Fintype X]
    (M : AddSubgroup (X → ZMod m)) (x : X) : AddSubgroup M :=
  (coordinateProjectionOnM m M x).ker

/-- The coordinate-translation action on `Ω = A × X`. -/
def coordinateTranslationAction (m : ℕ) [NeZero m] {X : Type*} [Fintype X]
    (u : X → ZMod m) (omega : ZMod m × X) : ZMod m × X :=
  (omega.1 + u omega.2, omega.2)

def coordinateTranslationActionOnM (m : ℕ) [NeZero m] {X : Type*} [Fintype X]
    (M : AddSubgroup (X → ZMod m)) (u : M) (omega : ZMod m × X) : ZMod m × X :=
  coordinateTranslationAction m u.1 omega

def coordinateFiber (x : X) : Set (ZMod m × X) :=
  {omega | omega.2 = x}

def coordinateOrbit (m : ℕ) [NeZero m] {X : Type*} [Fintype X]
    (M : AddSubgroup (X → ZMod m)) (omega : ZMod m × X) : Set (ZMod m × X) :=
  {target | ∃ u : M, coordinateTranslationActionOnM m M u omega = target}

/-- Claim 30931: the projection kernels and the subdirectness hypothesis in
    the coordinate-translation setup. -/
def coordinateTranslationSubdirectness (m : ℕ) [NeZero m]
    (X : Type*) [Fintype X] (M : AddSubgroup (X → ZMod m)) : Prop :=
  (∀ (u : X → ZMod m) (omega : ZMod m × X),
      coordinateTranslationAction m u omega =
        (omega.1 + u omega.2, omega.2)) ∧
    (∀ x : X, coordinateKernel m M x =
      (coordinateProjectionOnM m M x).ker) ∧
    (∀ x : X, Function.Surjective (coordinateProjectionOnM m M x))

/-- Claim 30932.  The unique quotient class in the last conjunct is the
    regular action of `M/K_x` on the fiber, while the additive equivalence
    records that the quotient is cyclic of order `m`. -/
def orbitQuotientLemma (m : ℕ) [NeZero m]
    (X : Type*) [Fintype X] (M : AddSubgroup (X → ZMod m)) : Prop :=
  coordinateTranslationSubdirectness m X M →
    (∀ (a : ZMod m) (x : X),
      coordinateOrbit m M (a, x) = coordinateFiber x) ∧
    (∀ (x : X) (a : ZMod m),
      {u : M | coordinateTranslationActionOnM m M u (a, x) = (a, x)} =
        (coordinateKernel m M x : Set M)) ∧
    (∀ x : X, Nonempty ((M ⧸ coordinateKernel m M x) ≃+ ZMod m)) ∧
    (∀ (x : X) (a y : ZMod m),
      ∃! q : M ⧸ coordinateKernel m M x,
        ∃ u : M,
          QuotientAddGroup.mk (s := coordinateKernel m M x) u = q ∧
            coordinateTranslationActionOnM m M u (a, x) = (y, x))

end R1307

namespace R1822

/-- The affine profile notion used in Claim 32633. -/
def affineOneCoordinateProfile {p : ℕ}
    (f : ZMod p → ZMod p) : Prop :=
  ∃ c d : ZMod p, ∀ t : ZMod p, f t = c * t + d

def normalizedOneCoordinateProfile {p : ℕ}
    (f : ZMod p → ZMod p) : Prop :=
  f 0 = 0

/-- Claim 32633. -/
def normalizedNonAffineOneCoordinateProfile
    (p : ℕ) (hp : Nat.Prime p) (f : ZMod p → ZMod p) : Prop :=
  normalizedOneCoordinateProfile f ∧
    ¬ affineOneCoordinateProfile f ∧
    (affineOneCoordinateProfile f ↔
      ∃ c : ZMod p, ∀ t : ZMod p, f t = c * t)

/-- The five-coordinate carrier in Claim 32634 is `F_p^5`. -/
def liftCorrection
    (p : ℕ) (hp : Nat.Prime p) (f : ZMod p → ZMod p) (lam : ZMod p)
    (x : Fin 5 → ZMod p) : Fin 5 → ZMod p :=
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  ![x 0 + f (x 2) + lam * x 1,
    x 1,
    x 2 + x 1 ^ 2 / (2 : ZMod p),
    x 3,
    x 4]

def uncorrectedReplacement
    (p : ℕ) (hp : Nat.Prime p) (f : ZMod p → ZMod p)
    (x : Fin 5 → ZMod p) : Fin 5 → ZMod p :=
  liftCorrection p hp f 0 x

/-- Claim 32634. -/
def familyOfLiftCorrections
    (p : ℕ) (hp : Nat.Prime p) (f : ZMod p → ZMod p) : Prop :=
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  normalizedNonAffineOneCoordinateProfile p hp f ∧
    (∀ (lam : ZMod p) (x : Fin 5 → ZMod p),
      liftCorrection p hp f lam x =
        ![x 0 + f (x 2) + lam * x 1,
          x 1,
          x 2 + x 1 ^ 2 / (2 : ZMod p),
          x 3,
          x 4]) ∧
    (∀ x : Fin 5 → ZMod p,
      uncorrectedReplacement p hp f x = liftCorrection p hp f 0 x)

end R1822

namespace R1875

/-- Members of a finite family containing a finite test set. -/
def membersContaining {alpha : Type*} [DecidableEq alpha]
    (G : Finset (Finset alpha)) (T : Finset alpha) : Finset (Finset alpha) :=
  G.filter (fun H => T ⊆ H)

def uniformFamily {alpha : Type*} [DecidableEq alpha]
    (G : Finset (Finset alpha)) (n : ℕ) : Prop :=
  ∀ H ∈ G, H.card = n

def threeSunflower {alpha : Type*} [DecidableEq alpha]
    (A B C : Finset alpha) : Prop :=
  A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C

def rSpread {alpha : Type*} [DecidableEq alpha]
    (G : Finset (Finset alpha)) (R : ℝ) : Prop :=
  1 < R ∧
    ∀ T : Finset alpha, T.Nonempty →
      (membersContaining G T).card ≤
        Real.rpow R (-(T.card : ℝ)) * (G.card : ℝ)

def indexSupport {alpha : Type*} [DecidableEq alpha]
    {m : ℕ} (A : Fin m → Finset alpha) (x : alpha) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x ∈ A i)

def coversIndexTriple {m : ℕ}
    (S I : Finset (Fin m)) : Prop :=
  I.card = 3 ∧ (S ∩ I).card = 2

def separatesIndexPair {m : ℕ}
    (S : Finset (Fin m)) (i j : Fin m) : Prop :=
  i ≠ j ∧ (S ∩ {i, j}).card = 1

/-- The exact definitional readings collected in Claim 34579. -/
def sunflowerSpreadSupportDefinitions
    (alpha : Type*) [DecidableEq alpha] : Prop :=
  (∀ (G : Finset (Finset alpha)) (n : ℕ),
      uniformFamily G n ↔ ∀ H ∈ G, H.card = n) ∧
    (∀ A B C : Finset alpha,
      threeSunflower A B C ↔
        (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
          A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)) ∧
    (∀ (G : Finset (Finset alpha)) (R : ℝ),
      rSpread G R ↔
        (1 < R ∧ ∀ T : Finset alpha, T.Nonempty →
          (membersContaining G T).card ≤
            Real.rpow R (-(T.card : ℝ)) * (G.card : ℝ))) ∧
    (∀ (m : ℕ) (A : Fin m → Finset alpha) (x : alpha),
      indexSupport A x = Finset.univ.filter (fun i => x ∈ A i)) ∧
    (∀ (m : ℕ) (S I : Finset (Fin m)),
      coversIndexTriple S I ↔ I.card = 3 ∧ (S ∩ I).card = 2) ∧
    (∀ (m : ℕ) (S : Finset (Fin m)) (i j : Fin m),
      separatesIndexPair S i j ↔
        i ≠ j ∧ (S ∩ {i, j}).card = 1)

def threeSunflowerFree {alpha : Type*} [DecidableEq alpha]
    (G : Finset (Finset alpha)) : Prop :=
  ¬ ∃ A B C : Finset alpha,
      A ∈ G ∧ B ∈ G ∧ C ∈ G ∧ threeSunflower A B C

def avoidanceSubfamily {alpha : Type*} [DecidableEq alpha]
    (G : Finset (Finset alpha)) (A : Finset alpha) : Finset (Finset alpha) :=
  G.filter (fun H => Disjoint H A)

def fiveCycleEdge (i : Fin 5) : Finset (Fin 5) :=
  {i, i + 1}

def fiveCycle : Finset (Finset (Fin 5)) :=
  Finset.univ.image fiveCycleEdge

/-- Claim 34584. -/
def avoidanceDoesNotInheritSpread : Prop :=
  let G := fiveCycle
  let pivot := fiveCycleEdge 0
  let avoidance := avoidanceSubfamily G pivot
  threeSunflowerFree G ∧
    rSpread G (Real.sqrt 5) ∧
    pivot ∈ G ∧
    (∀ v : Fin 5,
      (membersContaining G ({v} : Finset (Fin 5))).card = 2 ∧
        (2 : ℝ) ≤ 5 / Real.sqrt 5) ∧
    (∀ E : Finset (Fin 5), E ∈ G →
      (membersContaining G E).card = 1 ∧
        (1 : ℝ) = 5 / (Real.sqrt 5) ^ 2) ∧
    fiveCycleEdge 2 ∈ avoidance ∧
    fiveCycleEdge 3 ∈ avoidance ∧
    fiveCycleEdge 2 ∩ fiveCycleEdge 3 = ({3} : Finset (Fin 5)) ∧
    (∀ r : ℝ, 1 < r → ¬ rSpread avoidance r) ∧
    ¬ (∀ (H : Finset (Finset (Fin 5))) (R : ℝ) (A : Finset (Fin 5)),
      1 < R → threeSunflowerFree H → A ∈ H →
        rSpread H R → rSpread (avoidanceSubfamily H A) (R - 1))

end R1875

namespace R1901

abbrev CubeVertex (n : ℕ) := Fin n → ZMod 2

def cubeRelation (n : ℕ) (x y : CubeVertex n) : Prop :=
  ∃ i : Fin n, x i ≠ y i ∧
    ∀ k : Fin n, k ≠ i → x k = y k

def cubeGraph (n : ℕ) : SimpleGraph (CubeVertex n) :=
  SimpleGraph.fromRel (cubeRelation n)

abbrev edgeBase (n : ℕ) (i : Fin n) :=
  {x : CubeVertex n // x i = 0}

def basisVector (n : ℕ) (i : Fin n) : CubeVertex n :=
  fun k => if k = i then 1 else 0

def toggleCoordinate (n : ℕ) (x : CubeVertex n) (i : Fin n) : CubeVertex n :=
  x + basisVector n i

def edgeValue (n : ℕ)
    (f : ∀ i : Fin n, edgeBase n i → Fin 2)
    (i : Fin n) (x : CubeVertex n) (hx : x i = 0) : Fin 2 :=
  f i ⟨x, hx⟩

def edgeDensity (n : ℕ)
    (f : ∀ i : Fin n, edgeBase n i → Fin 2)
    (i : Fin n) : ℝ :=
  letI : Finite (edgeBase n i) := by infer_instance
  letI : Fintype (edgeBase n i) := Fintype.ofFinite _
  (∑ x : edgeBase n i, ((f i x).val : ℝ)) /
    (Fintype.card (edgeBase n i) : ℝ)

def coordinateEdgeEncoding (n : ℕ)
    (G : SimpleGraph (CubeVertex n))
    (f : ∀ i : Fin n, edgeBase n i → Fin 2) : Prop :=
  ∀ (i : Fin n) (x : edgeBase n i),
    (f i x).val =
      if G.Adj x.1 (toggleCoordinate n x.1 i) then 1 else 0

def coordinateSquareC4Free (n : ℕ)
    (f : ∀ i : Fin n, edgeBase n i → Fin 2) : Prop :=
  ∀ (i j : Fin n) (hij : i ≠ j) (x : CubeVertex n)
    (hi : x i = 0) (hj : x j = 0),
    (edgeValue n f i x hi).val *
        (edgeValue n f i (x + basisVector n j) (by
          simp [basisVector, hij, hi])).val *
        (edgeValue n f j x hj).val *
        (edgeValue n f j (x + basisVector n i) (by
          simp [basisVector, Ne.symm hij, hj])).val = 0

/-- Claim 34786. -/
def coordinateEdgeFunctionSetup (n : ℕ)
    (G : SimpleGraph (CubeVertex n))
    (f : ∀ i : Fin n, edgeBase n i → Fin 2)
    (p : Fin n → ℝ) : Prop :=
  G ≤ cubeGraph n ∧
    (p = fun i => edgeDensity n f i) ∧
    coordinateEdgeEncoding n G f ∧
    (Nat.card G.edgeSet : ℝ) =
      (2 : ℝ) ^ (n - 1) * ∑ i : Fin n, p i ∧
    coordinateSquareC4Free n f

/-- Claim 34788. -/
def fullDirectionExclusion (n : ℕ)
    (f : ∀ i : Fin n, edgeBase n i → Fin 2)
    (p : Fin n → ℝ) : Prop :=
  p = (fun i => edgeDensity n f i) →
    coordinateSquareC4Free n f →
      Set.ncard {i : Fin n | p i = 1} ≤ 1 ∧
      (∀ (i : Fin n),
        (∀ x : edgeBase n i, (f i x).val = 1) →
          ∀ (j : Fin n) (hij : i ≠ j),
            (∀ (x : CubeVertex n) (hi : x i = 0) (hj : x j = 0),
              ¬ ((edgeValue n f j x hj).val = 1 ∧
                (edgeValue n f j (x + basisVector n i) (by
                  simp [basisVector, Ne.symm hij, hj])).val = 1)) ∧
            p j ≤ (1 : ℝ) / 2 ∧ p j < (3 : ℝ) / 4)

end R1901

namespace R1875

/-- Pairwise intersection for a finite family, used in Claim 34886. -/
def pairwiseIntersecting {alpha : Type*} [DecidableEq alpha]
    (G : Finset (Finset alpha)) : Prop :=
  ∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).Nonempty

/-- Claim 34886. -/
def pooledResidualsNeedNotBeDistinct : Prop :=
  let family : Finset (Finset (Fin 3)) :=
    {{0, 1}, {0, 2}, {1, 2}}
  let pivot : Finset (Fin 3) := {0, 1}
  let first : Finset (Fin 3) := {0, 2}
  let second : Finset (Fin 3) := {1, 2}
  pairwiseIntersecting family ∧
    threeSunflowerFree family ∧
    pivot ∈ family ∧ first ∈ family ∧ second ∈ family ∧
    first ≠ second ∧
    first ∩ pivot = ({0} : Finset (Fin 3)) ∧
    second ∩ pivot = ({1} : Finset (Fin 3)) ∧
    first \ pivot = ({2} : Finset (Fin 3)) ∧
    second \ pivot = ({2} : Finset (Fin 3)) ∧
    first \ pivot = second \ pivot ∧
    ∃ A B : Finset (Fin 3),
      A ∈ family ∧ B ∈ family ∧ A ≠ B ∧ A \ pivot = B \ pivot

end R1875

end ResearchFormalizationBatch
end Open
end MathlibPlus
