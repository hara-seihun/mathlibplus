import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2006.Claim35200

abbrev F2 := ZMod 2
abbrev Cube (n : ℕ) := Fin n → F2
abbrev Dual (V : Type*) [AddCommMonoid V] [Module F2 V] := V →ₗ[F2] F2

def coordinateCharacter {n : ℕ} (k : Fin n) : Dual (Cube n) :=
  LinearMap.proj k

def vanishingCoordinates {n : ℕ} (s : Finset (Fin n)) : Submodule F2 (Cube n) :=
  s.inf fun k => LinearMap.ker (coordinateCharacter k)

def pairMap {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j) :
    Cube n →ₗ[F2] W_i × W_j :=
  F_i.prod F_j

def pairImage {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (s : Finset (Fin n)) : Submodule F2 (W_i × W_j) :=
  Submodule.map (pairMap F_i F_j) (vanishingCoordinates s)

def pairAnnihilator {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (s : Finset (Fin n)) : Set (Dual W_i × Dual W_j) :=
  {p | ∀ x, x ∈ vanishingCoordinates s →
    p.1 (F_i x) + p.2 (F_j x) = 0}

def pullbackPair {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (p : Dual W_i × Dual W_j) : Dual (Cube n) :=
  p.1.comp F_i + p.2.comp F_j

def coordinateAugmentedImage {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module F2 W]
    (F : Cube n →ₗ[F2] W) (i : Fin n) : Set (Dual (Cube n)) :=
  {f | ∃ α : Dual W, ∃ a : F2,
    f = α.comp F + a • coordinateCharacter i}

def setAdd {V : Type*} [AddCommGroup V] (A B : Set V) : Set V :=
  {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

def nonzeroThirdRelation {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (i j k : Fin n) (annP : Set (Dual W_i × Dual W_j)) : Prop :=
  ∃ p ∈ annP, ∃ a b c : F2,
    pullbackPair F_i F_j p =
      a • coordinateCharacter i + b • coordinateCharacter j +
        c • coordinateCharacter k ∧ c ≠ 0

def differenceWitness {V : Type*} (A B : Set V) : Prop :=
  ∃ x, x ∈ A ∧ x ∉ B

/-- The pullback-span identities and the exact defective-deletion criterion. -/
def claim35200_exactDualDefectiveDeletionCriterion : Prop :=
  ∀ (n : ℕ) (W_i W_j : Type*)
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (i j k : Fin n),
    i ≠ j → i ≠ k → j ≠ k →
    let annM := pairAnnihilator F_i F_j {i, j}
    let annP := pairAnnihilator F_i F_j {i, j, k}
    let spanIJ := Submodule.span F2
      ({coordinateCharacter i, coordinateCharacter j} : Set (Dual (Cube n)))
    let spanIJK := Submodule.span F2
      ({coordinateCharacter i, coordinateCharacter j, coordinateCharacter k} :
        Set (Dual (Cube n)))
    let A_i := coordinateAugmentedImage F_i i
    let A_j := coordinateAugmentedImage F_j j
    annM = {p | pullbackPair F_i F_j p ∈ spanIJ} ∧
      annP = {p | pullbackPair F_i F_j p ∈ spanIJK} ∧
      (annP ≠ annM ↔ nonzeroThirdRelation F_i F_j i j k annP) ∧
      (annP ≠ annM ↔
        coordinateCharacter k ∈ setAdd A_i A_j) ∧
      (coordinateCharacter k ∈ setAdd A_i A_j ↔
        differenceWitness annP annM) ∧
      (pairImage F_i F_j {i, j, k} ≠ pairImage F_i F_j {i, j} ↔
        coordinateCharacter k ∈ setAdd A_i A_j)

end MathlibPlus.Open.ResearchFormalization.R2006.Claim35200
