import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim35149

noncomputable section
open Classical

abbrev F2 := ZMod 2
abbrev CoordinateSpace (n : ℕ) := Fin n → F2
abbrev CoordinateDual (n : ℕ) := Module.Dual F2 (CoordinateSpace n)

def coordinateVector (n : ℕ) (i : Fin n) : CoordinateSpace n :=
  Pi.single i 1

def coordinateCharacter (n : ℕ) (i : Fin n) : CoordinateDual n :=
  LinearMap.proj i

def pullbackSpace {n : ℕ} {W : Fin n → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i) (i : Fin n) :
    Submodule F2 (CoordinateDual n) :=
  LinearMap.range (Fmap i).dualMap

def enlargedSpace {n : ℕ} {W : Fin n → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i) (i : Fin n) :
    Submodule F2 (CoordinateDual n) :=
  pullbackSpace Fmap i ⊔ Submodule.span F2 {coordinateCharacter n i}

def pairBase (n : ℕ) (i j : Fin n) : Submodule F2 (CoordinateSpace n) :=
  LinearMap.ker (coordinateCharacter n i) ⊓ LinearMap.ker (coordinateCharacter n j)

def pairImage {n : ℕ} {W : Fin n → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i)
    (i j : Fin n) : Submodule F2 (W i × W j) :=
  LinearMap.range
    ((LinearMap.prod (Fmap i) (Fmap j)).comp ((pairBase n i j).subtype))

def coordinateRestriction (n : ℕ)
    (C : Submodule F2 (CoordinateDual n)) (j : Fin n) :
    C →ₗ[F2] F2 :=
  (LinearMap.applyₗ (R := F2) (M := CoordinateSpace n) (M₂ := F2)
    (coordinateVector n j)).comp C.subtype

def commonCenterPairRelation_claim35149 : Prop :=
  ∀ (n : ℕ) (W : Fin n → Type*)
    [∀ i, AddCommGroup (W i)]
    [∀ i, Module F2 (W i)]
    [∀ i, Module.Finite F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i)
    (I : Finset (Fin n))
    (C : Submodule F2 (CoordinateDual n)),
    (∀ i : Fin n, Function.Surjective (Fmap i)) →
    (∀ i : Fin n, Fmap i (coordinateVector n i) = 0) →
    (∀ i : Fin n, i ∈ I → C ≤ enlargedSpace Fmap i) →
    (∀ i j : Fin n, i ∈ I → j ∈ I → i ≠ j →
      enlargedSpace Fmap i ⊓ enlargedSpace Fmap j = C) →
    ∃ lambda : ∀ i : {i : Fin n // i ∈ I},
        C →ₗ[F2] Module.Dual F2 (W (i : Fin n)),
      ∃ c : ∀ i : {i : Fin n // i ∈ I}, C →ₗ[F2] F2,
        ∃ theta : ∀ i : {i : Fin n // i ∈ I},
            W (i : Fin n) →ₗ[F2] Module.Dual F2 C,
          (∀ i : {i : Fin n // i ∈ I}, ∀ z : C,
            (Fmap (i : Fin n)).dualMap (lambda i z) +
                c i z • coordinateCharacter n (i : Fin n) = (z : CoordinateDual n) ∧
            (∀ (α : Module.Dual F2 (W (i : Fin n))) (d : F2),
              (Fmap (i : Fin n)).dualMap α +
                  d • coordinateCharacter n (i : Fin n) = (z : CoordinateDual n) →
                α = lambda i z ∧ d = c i z)) ∧
          (∀ i : {i : Fin n // i ∈ I},
            coordinateCharacter n (i : Fin n) ∉ C →
              Function.Injective (lambda i) ∧ Function.Surjective (theta i)) ∧
          (∀ i : {i : Fin n // i ∈ I}, ∀ w : W (i : Fin n), ∀ z : C,
            theta i w z = lambda i z w) ∧
          (∀ i j : {i : Fin n // i ∈ I}, i ≠ j →
            ∀ x : W (i : Fin n), ∀ y : W (j : Fin n),
              (x, y) ∈ pairImage Fmap (i : Fin n) (j : Fin n) ↔
                theta i x = theta j y) ∧
          (∀ i j : {i : Fin n // i ∈ I}, i ≠ j →
            theta i (Fmap (i : Fin n) (coordinateVector n (j : Fin n))) =
              coordinateRestriction n C (j : Fin n)) ∧
          Set.ncard {i : Fin n | i ∈ I ∧ coordinateCharacter n i ∈ C} ≤
            Module.finrank F2 C

end
end MathlibPlus.Open.LinearAlgebra.Claim35149
