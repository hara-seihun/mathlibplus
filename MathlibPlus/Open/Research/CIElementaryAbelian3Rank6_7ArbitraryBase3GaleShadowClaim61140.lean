import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.CIElementaryAbelian3Rank6_7ArbitraryBase3GaleShadow

noncomputable section

abbrev F3 := ZMod 3
abbrev B := Fin 3 → F3
abbrev A := Fin 4 → F3
abbrev G := A × B

/-- The seven columns of `[I_3 | X]`, with `X` a `3` by `4` matrix. -/
def galeDirection (X : Matrix (Fin 3) (Fin 4) F3) : Fin 7 → B
  | 0 => Pi.single 0 1
  | 1 => Pi.single 1 1
  | 2 => Pi.single 2 1
  | 3 => fun j => X j 0
  | 4 => fun j => X j 1
  | 5 => fun j => X j 2
  | 6 => fun j => X j 3

/-- The seven covectors, the columns of `[-Xᵀ | I₄]`. -/
def galeCovector (X : Matrix (Fin 3) (Fin 4) F3) :
    Fin 7 → (A →ₗ[F3] F3)
  | 0 => ∑ k : Fin 4, (-X 0 k) •
      (LinearMap.proj k : A →ₗ[F3] F3)
  | 1 => ∑ k : Fin 4, (-X 1 k) •
      (LinearMap.proj k : A →ₗ[F3] F3)
  | 2 => ∑ k : Fin 4, (-X 2 k) •
      (LinearMap.proj k : A →ₗ[F3] F3)
  | 3 => (LinearMap.proj 0 : A →ₗ[F3] F3)
  | 4 => (LinearMap.proj 1 : A →ₗ[F3] F3)
  | 5 => (LinearMap.proj 2 : A →ₗ[F3] F3)
  | 6 => (LinearMap.proj 3 : A →ₗ[F3] F3)

def galeTensor (X : Matrix (Fin 3) (Fin 4) F3) (i : Fin 7) :
    TensorProduct F3 (A →ₗ[F3] F3) B :=
  TensorProduct.tmul F3 (galeCovector X i) (galeDirection X i)

def galeNonzero (X : Matrix (Fin 3) (Fin 4) F3) : Prop :=
  ∀ i : Fin 7,
    galeDirection X i ≠ 0 ∧ galeCovector X i ≠ 0

def galeTensorRankSix (X : Matrix (Fin 3) (Fin 4) F3) : Prop :=
  Module.finrank F3
      (Submodule.span F3 (Set.range (galeTensor X))) = 6

def galeTensorSumZero (X : Matrix (Fin 3) (Fin 4) F3) : Prop :=
  (∑ i : Fin 7, galeTensor X i) = 0

def galeTensorUniqueDependence (X : Matrix (Fin 3) (Fin 4) F3) : Prop :=
  ∀ c : Fin 7 → F3,
    (∑ i : Fin 7, c i • galeTensor X i = 0) →
      ∃ r : F3, ∀ i : Fin 7, c i = r

def hyperplaneFibreConnectionSet
    (X : Matrix (Fin 3) (Fin 4) F3) (c : Fin 7 → F3) : Set G :=
  {q | ∃ i : Fin 7,
    (q.2 = galeDirection X i ∧
      galeCovector X i q.1 = c i) ∨
    (q.2 = -galeDirection X i ∧
      galeCovector X i q.1 = -c i)}

def verticalShear (F : B → A) : G → G :=
  fun q => (q.1 + F q.2, q.2)

def groupLinearShear (L : B →ₗ[F3] A) : G → G :=
  fun q => (q.1 + L q.2, q.2)

def shearDifference (F : B → A) (x : B) (q : G) : G :=
  (q.1 + F (x + q.2) - F x, q.2)

def shearTargetConnectionSet (F : B → A)
    (X : Matrix (Fin 3) (Fin 4) F3) : Set G :=
  {q | ∃ x : B, ∃ s : G,
    s ∈ hyperplaneFibreConnectionSet X (fun _ => 0) ∧
      q = shearDifference F x s}

def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

def cayleyIsomorphism (S T : Set G) (f : G → G) : Prop :=
  Function.Bijective f ∧
    ∀ x y : G,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def inverseClosed (S : Set G) : Prop :=
  ∀ ⦃s : G⦄, s ∈ S → -s ∈ S

def identityFree (S : Set G) : Prop :=
  (0 : G) ∉ S

def ordinaryUndirectedCayleyCIDefect
    (S T : Set G) (f : G → G) : Prop :=
  identityFree S ∧
    identityFree T ∧
    inverseClosed S ∧
    inverseClosed T ∧
    cayleyIsomorphism S T f ∧
    ¬ ∃ e : G ≃+ G, e '' S = T

/-- The arbitrary-table `3+4` seven-row Gale-shadow theorem. -/
def claim61140 : Prop :=
  (∀ X : Matrix (Fin 3) (Fin 4) F3,
    galeTensorSumZero X) ∧
  ∀ X : Matrix (Fin 3) (Fin 4) F3,
    galeNonzero X →
      galeTensorRankSix X →
        galeTensorUniqueDependence X ∧
        ∀ F : B → A,
          ∀ lambda : Fin 7 → F3,
            (∀ x : B, ∀ i : Fin 7,
              galeCovector X i (F (x + galeDirection X i) - F x) =
                lambda i) →
              (∑ i : Fin 7, lambda i = 0) ∧
              ∃ L : B →ₗ[F3] A,
                (∀ i : Fin 7,
                  galeCovector X i (L (galeDirection X i)) = lambda i) ∧
                shearTargetConnectionSet F X =
                  hyperplaneFibreConnectionSet X lambda ∧
                shearTargetConnectionSet (fun x => L x) X =
                  hyperplaneFibreConnectionSet X lambda ∧
                shearTargetConnectionSet F X =
                  shearTargetConnectionSet (fun x => L x) X ∧
                ¬ ordinaryUndirectedCayleyCIDefect
                    (hyperplaneFibreConnectionSet X (fun _ => 0))
                    (shearTargetConnectionSet F X)
                    (verticalShear F)

end
end MathlibPlus.Open.Research.CIElementaryAbelian3Rank6_7ArbitraryBase3GaleShadow
