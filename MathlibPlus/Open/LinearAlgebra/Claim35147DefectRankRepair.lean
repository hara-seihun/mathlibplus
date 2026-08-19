import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim35147

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

def deletedPairImage {n : ℕ} {W : Fin n → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i)
    (i j k : Fin n) : Submodule F2 (W i × W j) :=
  LinearMap.range
    ((LinearMap.prod (Fmap i) (Fmap j)).comp
      ((pairBase n i j ⊓ LinearMap.ker (coordinateCharacter n k)).subtype))

def defectSet {n : ℕ} {W : Fin n → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i)
    (i j : Fin n) : Set (Fin n) :=
  {k | k ≠ i ∧ k ≠ j ∧
    deletedPairImage Fmap i j k ≠ pairImage Fmap i j}

def sharpDefectiveCoordinateRankBound_claim35147 : Prop :=
  ∀ (n : ℕ) (W : Fin n → Type*)
    [∀ i, AddCommGroup (W i)]
    [∀ i, Module F2 (W i)]
    [∀ i, Module.Finite F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i)
    (r : Fin n → ℕ),
    (∀ i : Fin n, Function.Surjective (Fmap i)) →
    (∀ i : Fin n, Fmap i (coordinateVector n i) = 0) →
    (∀ i : Fin n, Module.finrank F2 (W i) = r i) →
    (∀ i j : Fin n, i ≠ j →
      Set.ncard (defectSet Fmap i j) ≤
          r i + r j -
            Module.finrank F2 (Submodule.dualAnnihilator (pairImage Fmap i j)) ∧
        Set.ncard (defectSet Fmap i j) ≤ r i + r j) ∧
    (∀ q : ℕ, (∀ i : Fin n, r i ≤ q) →
      ∀ i j : Fin n, i ≠ j → Set.ncard (defectSet Fmap i j) ≤ 2 * q)

end
end MathlibPlus.Open.LinearAlgebra.Claim35147
