import Mathlib

namespace MathlibPlus.Open.HallMarker

universe u v

variable {A : Type u} {B : Type v}

 def symmetricColoring [AddGroup A] (k : ℕ) (color : A → Fin k)
    (hpos : 0 < k) : Prop :=
  color 0 = (⟨0, hpos⟩ : Fin k) ∧ ∀ a : A, color (-a) = color a

def markerFamily [Fintype B] [AddGroup B] (k : ℕ) (F : Fin k → Set B)
    (hpos : 0 < k) : Prop :=
  (k ≤ Fintype.card B + 1) ∧
    (0 ∉ F ⟨0, hpos⟩) ∧
    ∀ i : Fin k,
      (∀ b : B, b ∈ F i → -b ∈ F i) ∧
        Set.ncard (F i) = i.val

def hallMarkerSet [AddGroup A] [AddGroup B] {k : ℕ}
    (F : Fin k → Set B) (color : A → Fin k) : Set (A × B) :=
  {x | x.2 ∈ F (color x.1)}

def identityFree {G : Type*} (zero : G) (S : Set G) : Prop :=
  zero ∉ S

def inverseClosed [Neg G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def addCayleyAdj [AddGroup G] (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

def firstCoordinateMap {A : Type u} {B : Type v} (φ : A → A) : A × B → A × B :=
  fun x => (φ x.1, x.2)

def graphIsomorphismByFirstCoordinate [AddGroup A] [AddGroup B]
    (S T : Set (A × B)) (φ : A → A) : Prop :=
  Function.Bijective (firstCoordinateMap (B := B) φ) ∧
    ∀ x y : A × B,
      addCayleyAdj S x y ↔
        addCayleyAdj T (firstCoordinateMap (B := B) φ x) (firstCoordinateMap (B := B) φ y)

def sectionOver {A : Type u} {B : Type v} (S : Set (A × B)) (a : A) : Set B :=
  {b | (a, b) ∈ S}

def hasActualImageSectionTransporter [AddGroup A] [AddGroup B]
    (S T : Set (A × B)) : Prop :=
  ∃ (α : A ≃+ A) (β : B ≃+ B),
    ∀ a : A, β '' sectionOver S a = sectionOver T (α a)

/-- Claim 57669: a symmetric colour defect lifts to the stated graph defect. -/
def claim_57669 [Fintype A] [Fintype B] [AddGroup A] [AddGroup B]
    (k : ℕ) (F : Fin k → Set B) (kappa lambda : A → Fin k)
    (hpos : 0 < k) : Prop :=
  (symmetricColoring k kappa hpos ∧ symmetricColoring k lambda hpos ∧
      markerFamily k F hpos) →
    let Skappa := hallMarkerSet F kappa
    let Slambda := hallMarkerSet F lambda
    identityFree (0 : A × B) Skappa ∧
      identityFree (0 : A × B) Slambda ∧
      inverseClosed Skappa ∧ inverseClosed Slambda ∧
      (∀ φ : A → A,
        (Function.Bijective φ ∧
            (∀ x y : A, kappa (x - y) = lambda (φ x - φ y))) →
          graphIsomorphismByFirstCoordinate Skappa Slambda φ) ∧
      ((¬ ∃ α : A ≃+ A, ∀ a : A, lambda (α a) = kappa a) →
        ¬ hasActualImageSectionTransporter Skappa Slambda)

end MathlibPlus.Open.HallMarker
