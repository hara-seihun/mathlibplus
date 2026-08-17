import Mathlib

namespace MathlibPlus.Open.Research.BatchR1989

noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev F2_35086 := ZMod 2
abbrev Cube_35086 (n : ℕ) := Fin n → F2_35086
abbrev Face_35086 (n : ℕ) (i : Fin n) := {x : Cube_35086 n // x i = 0}

/-- The literal coordinate vector in the binary cube. -/
def cubeBasis_35086 (n : ℕ) (i : Fin n) : Cube_35086 n :=
  fun j => if j = i then 1 else 0

/-- Translation of a subset by the displayed binary displacement. -/
def translateSet_35086 {W : Type*} [Add W]
    (S : Set W) (v : W) : Set W :=
  {x | ∃ y, y ∈ S ∧ y + v = x}

/-- The complete quotient autocorrelation event `C_S(v) = S ∩ (S + v)`. -/
def completeAutocorrelation_35086 {W : Type*} [Add W]
    (S : Set W) (v : W) : Set W :=
  S ∩ translateSet_35086 S v

/-- Exactness of a binary stabilizer quotient, including its coordinate
factorization and the trivial stabilizer of the descended selected set. -/
def exactStabilizerQuotient_35086 {n : ℕ} {i : Fin n}
    {W : Type*} [AddCommGroup W] [Module F2_35086 W]
    (g : Face_35086 n i → F2_35086)
    (F : Cube_35086 n →ₗ[F2_35086] W) (S : Set W) : Prop :=
  Function.Surjective F ∧
    F (cubeBasis_35086 n i) = 0 ∧
    (∀ x : Face_35086 n i,
      g x = if F x.1 ∈ S then 1 else 0) ∧
    (∀ v : W,
      (∀ w : W, w ∈ S ↔ w + v ∈ S) → v = 0)

/-- The exact joint image on the two coordinate-vanishing face. -/
def pairImage_35086 {n : ℕ}
    {Wᵢ Wⱼ : Type*}
    [AddCommGroup Wᵢ] [Module F2_35086 Wᵢ]
    [AddCommGroup Wⱼ] [Module F2_35086 Wⱼ]
    (i j : Fin n)
    (Fᵢ : Cube_35086 n →ₗ[F2_35086] Wᵢ)
    (Fⱼ : Cube_35086 n →ₗ[F2_35086] Wⱼ) : Set (Wᵢ × Wⱼ) :=
  {p | ∃ x : Cube_35086 n,
    x i = 0 ∧ x j = 0 ∧ (Fᵢ x, Fⱼ x) = p}

/-- Claim 35086: exact quotient dimensions, displacements, joint image, and
lossless square/product avoidance are retained together. -/
def claim_35086 {n : ℕ} (i j : Fin n)
    {Wᵢ Wⱼ : Type*}
    [Fintype Wᵢ] [AddCommGroup Wᵢ] [Module F2_35086 Wᵢ]
    [FiniteDimensional F2_35086 Wᵢ]
    [Fintype Wⱼ] [AddCommGroup Wⱼ] [Module F2_35086 Wⱼ]
    [FiniteDimensional F2_35086 Wⱼ]
    (gᵢ : Face_35086 n i → F2_35086)
    (gⱼ : Face_35086 n j → F2_35086)
    (Fᵢ : Cube_35086 n →ₗ[F2_35086] Wᵢ)
    (Fⱼ : Cube_35086 n →ₗ[F2_35086] Wⱼ)
    (Sᵢ : Set Wᵢ) (Sⱼ : Set Wⱼ)
    (dᵢ dⱼ : ℕ) (aᵢⱼ : Wᵢ) (bᵢⱼ : Wⱼ)
    (Mᵢⱼ : Set (Wᵢ × Wⱼ)) : Prop :=
  i < j ∧
    dᵢ = Module.finrank F2_35086 Wᵢ ∧
    dⱼ = Module.finrank F2_35086 Wⱼ ∧
    exactStabilizerQuotient_35086 gᵢ Fᵢ Sᵢ ∧
    exactStabilizerQuotient_35086 gⱼ Fⱼ Sⱼ ∧
    aᵢⱼ = Fᵢ (cubeBasis_35086 n j) ∧
    bᵢⱼ = Fⱼ (cubeBasis_35086 n i) ∧
    Mᵢⱼ = pairImage_35086 i j Fᵢ Fⱼ ∧
    Mᵢⱼ ∩
        (completeAutocorrelation_35086 Sᵢ aᵢⱼ ×ˢ
          completeAutocorrelation_35086 Sⱼ bᵢⱼ) = ∅

end
end MathlibPlus.Open.Research.BatchR1989
