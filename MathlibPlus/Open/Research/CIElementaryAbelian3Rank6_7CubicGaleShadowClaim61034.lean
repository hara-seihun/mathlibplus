import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.CIElementaryAbelian3Rank6_7CubicGaleShadow

noncomputable section

abbrev F3 := ZMod 3
abbrev A := Fin 3 → F3
abbrev B := Fin 4 → F3
abbrev G := A × B

/-- The exponent vectors of the sixteen reduced homogeneous cubic monomials. -/
abbrev ReducedCubicExponent :=
  {e : Fin 4 → Fin 3 // ∑ j : Fin 4, (e j).val = 3}

def galeDirection (X : Matrix (Fin 4) (Fin 3) F3) : Fin 7 → B
  | 0 => Pi.single 0 1
  | 1 => Pi.single 1 1
  | 2 => Pi.single 2 1
  | 3 => Pi.single 3 1
  | 4 => fun j => X j 0
  | 5 => fun j => X j 1
  | 6 => fun j => X j 2

def galeCovector (X : Matrix (Fin 4) (Fin 3) F3) :
    Fin 7 → (A →ₗ[F3] F3)
  | 0 => ∑ j : Fin 3, (-X 0 j) • LinearMap.proj j
  | 1 => ∑ j : Fin 3, (-X 1 j) • LinearMap.proj j
  | 2 => ∑ j : Fin 3, (-X 2 j) • LinearMap.proj j
  | 3 => ∑ j : Fin 3, (-X 3 j) • LinearMap.proj j
  | 4 => LinearMap.proj 0
  | 5 => LinearMap.proj 1
  | 6 => LinearMap.proj 2

def galeTensor (X : Matrix (Fin 4) (Fin 3) F3) (i : Fin 7) :
    TensorProduct F3 (A →ₗ[F3] F3) B :=
  TensorProduct.tmul F3 (galeCovector X i) (galeDirection X i)

def galeTensorRankSix (X : Matrix (Fin 4) (Fin 3) F3) : Prop :=
  Module.finrank F3
      (Submodule.span F3 (Set.range (galeTensor X))) = 6

def galeTensorSumZero (X : Matrix (Fin 4) (Fin 3) F3) : Prop :=
  (∑ i : Fin 7, galeTensor X i) = 0

def reducedCubicEvaluation
    (coeff : Fin 3 → ReducedCubicExponent → F3) (x : B) : A :=
  fun k => ∑ e : ReducedCubicExponent,
    coeff k e • ∏ j : Fin 4, (x j) ^ (e.1 j).val

def isReducedHomogeneousCubic (F : B → A) : Prop :=
  ∃ linearCoeff : Fin 3 → Fin 4 → F3,
    ∃ cubicCoeff : Fin 3 → ReducedCubicExponent → F3,
      ∀ x : B, ∀ k : Fin 3,
        F x k =
          (∑ j : Fin 4, linearCoeff k j * (x j) ^ 3) +
            reducedCubicEvaluation cubicCoeff x k

def hyperplaneFibreConnectionSet
    (X : Matrix (Fin 4) (Fin 3) F3) (c : Fin 7 → F3) : Set G :=
  {q | ∃ i : Fin 7,
    (q.2 = galeDirection X i ∧
      galeCovector X i q.1 = c i) ∨
    (q.2 = -galeDirection X i ∧
      galeCovector X i q.1 = -c i)}

def nonlinearShear (F : B → A) : G → G :=
  fun q => (q.1 + F q.2, q.2)

def groupLinearShear (L : B →ₗ[F3] A) : G → G :=
  fun q => (q.1 + L q.2, q.2)

def shearDifference (F : B → A) (x : B) (q : G) : G :=
  (q.1 + F (x + q.2) - F x, q.2)

def shearTargetConnectionSet (F : B → A)
    (X : Matrix (Fin 4) (Fin 3) F3) : Set G :=
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

def claim61034 : Prop :=
  (∀ X : Matrix (Fin 4) (Fin 3) F3, galeTensorSumZero X) ∧
  ∀ X : Matrix (Fin 4) (Fin 3) F3,
    galeTensorRankSix X →
      ∀ F : B → A,
        isReducedHomogeneousCubic F →
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
                shearTargetConnectionSet F X =
                  shearTargetConnectionSet (fun x => L x) X ∧
                (∃ e : G ≃+ G,
                  (∀ q : G, e q = groupLinearShear L q) ∧
                  e '' hyperplaneFibreConnectionSet X (fun _ => 0) =
                    shearTargetConnectionSet F X) ∧
                ¬ ordinaryUndirectedCayleyCIDefect
                    (hyperplaneFibreConnectionSet X (fun _ => 0))
                    (shearTargetConnectionSet F X)
                    (nonlinearShear F)

end
end MathlibPlus.Open.Research.CIElementaryAbelian3Rank6_7CubicGaleShadow
