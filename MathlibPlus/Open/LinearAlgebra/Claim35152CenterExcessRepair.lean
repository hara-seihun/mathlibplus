import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim35152

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

def coordinateRestriction (n : ℕ)
    (C : Submodule F2 (CoordinateDual n)) (j : Fin n) :
    C →ₗ[F2] F2 :=
  (LinearMap.applyₗ (R := F2) (M := CoordinateSpace n) (M₂ := F2)
    (coordinateVector n j)).comp C.subtype

def exceptionalIndices (n : ℕ) (I : Finset (Fin n))
    (C : Submodule F2 (CoordinateDual n)) : Finset (Fin n) :=
  I.filter (fun i => coordinateCharacter n i ∈ C)

def centerLabelClass (n : ℕ) (I : Finset (Fin n))
    (C : Submodule F2 (CoordinateDual n))
    (q : Module.Dual F2 C) : Finset (Fin n) :=
  I.filter (fun i =>
    coordinateCharacter n i ∉ C ∧ coordinateRestriction n C i = q)

def commonCenterBlockExcessBound_claim35152 : Prop :=
  ∀ (n : ℕ) (W : Fin n → Type*)
    [∀ i, AddCommGroup (W i)]
    [∀ i, Module F2 (W i)]
    [∀ i, Module.Finite F2 (W i)]
    (Fmap : ∀ i : Fin n, CoordinateSpace n →ₗ[F2] W i)
    (I : Finset (Fin n))
    (C : Submodule F2 (CoordinateDual n))
    (p : Fin n → ℚ),
    (∀ i : Fin n, Function.Surjective (Fmap i)) →
    (∀ i : Fin n, Fmap i (coordinateVector n i) = 0) →
    (2 ≤ I.card) →
    (∀ i : Fin n, i ∈ I → C ≤ enlargedSpace Fmap i) →
    (∀ i j : Fin n, i ∈ I → j ∈ I → i ≠ j →
      enlargedSpace Fmap i ⊓ enlargedSpace Fmap j = C) →
    (∀ i : Fin n, i ∈ I → 0 ≤ p i ∧ p i ≤ 1) →
    (∀ q : Module.Dual F2 C,
      (∑ i ∈ centerLabelClass n I C q, p i) ≤
        (centerLabelClass n I C q).card / 2 + 1 / 2) →
    (exceptionalIndices n I C).card ≤ Module.finrank F2 C ∧
    Nat.card (Module.Dual F2 C) = 2 ^ Module.finrank F2 C ∧
    (∑ i ∈ I, p i) ≤
      (I.card : ℚ) / 2 +
        (2 : ℚ) ^ Module.finrank F2 C / 2 +
        (Module.finrank F2 C : ℚ) / 2 ∧
    (∀ r : ℕ,
      (∀ i : Fin n, i ∈ I → Module.finrank F2 (W i) ≤ r) →
        Module.finrank F2 C ≤ r + 1 ∧
        (∑ i ∈ I, p i) ≤
          (I.card : ℚ) / 2 + (2 : ℚ) ^ r +
            ((r + 1 : ℕ) : ℚ) / 2)

end
end MathlibPlus.Open.LinearAlgebra.Claim35152
