import Mathlib

namespace MathlibPlus.Open.Research

/-- Transitivity of a permutation subgroup on its carrier. -/
def transitiveOn {V : Type*}
    (X : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ a b : V, ∃ g : X, g.1 a = b

/-- An ambient group preserves the three blocks indexed by `Fin 3`. -/
def preservesThreeBlocks {V : Type*} [Fintype V]
    (X : Subgroup (Equiv.Perm (V × Fin 3))) : Prop :=
  ∀ g : X, ∀ i : Fin 3, ∃ j : Fin 3, ∀ x : V,
    (g.1 (x, i)).2 = j

/-- The subgroup fixing each of the three blocks pointwise as blocks. -/
def isThreeBlockKernel {V : Type*}
    (X K : Subgroup (Equiv.Perm (V × Fin 3))) : Prop :=
  K ≤ X ∧
    (∀ k : K, ∀ x : V, ∀ i : Fin 3, (k.1 (x, i)).2 = i) ∧
    (∀ g : X, (∀ x : V, ∀ i : Fin 3, (g.1 (x, i)).2 = i) → g.1 ∈ K)

/-- Normality of a subgroup relative to a subgroup of the ambient permutation
 group. -/
def normalIn {G : Type*} [Group G]
    (N X : Subgroup G) : Prop :=
  ∀ g : X, ∀ n : N, g.1 * n.1 * g.1⁻¹ ∈ N

/-- The diagonal regular translation condition for the normal elementary-abelian
translation group. -/
def isDiagonalTranslationGroup {p : ℕ} {V : Type*} [AddCommGroup V]
    (N : Subgroup (Equiv.Perm (V × Fin 3))) : Prop :=
  (∀ n : N, ∃ t : V, ∀ x : V, ∀ i : Fin 3,
      n.1 (x, i) = (x + t, i)) ∧
    (∀ t : V, ∃ n : N, ∀ x : V, ∀ i : Fin 3,
      n.1 (x, i) = (x + t, i)) ∧
    ∀ n : N, n.1 ^ p = 1

/-- An affine action on a block, with irreducible point stabilizer. -/
def primitiveAffineBlockAction {𝕜 V : Type*} [Fintype V]
    [AddCommGroup V] [Field 𝕜] [Module 𝕜 V]
    (K : Subgroup (Equiv.Perm (V × Fin 3))) : Prop :=
  (∀ k : K, ∀ i : Fin 3, ∃ A : V ≃ₗ[𝕜] V, ∃ b : V,
      ∀ x : V, (k.1 (x, i)).1 = A x + b) ∧
    (∀ i : Fin 3, ∀ W : Submodule 𝕜 V,
      (∀ k : K, k.1 (0, i) = (0, i) →
        ∀ x : V, x ∈ W → (k.1 (x, i)).1 ∈ W) →
      W = ⊥ ∨ W = ⊤)

def commonLinearImageIrreducible {𝕜 V K : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (A : K → V ≃ₗ[𝕜] V) : Prop :=
  ∀ W : Submodule 𝕜 V,
    (∀ k : K, ∀ x : V, x ∈ W → A k x ∈ W) → W = ⊥ ∨ W = ⊤

def diagonalTranslate {V : Type*} [AddGroup V] (t : V) :
    Equiv.Perm (V × Fin 3) :=
  Equiv.prodCongr (Equiv.addRight t) (Equiv.refl (Fin 3))

/-- Claim 51892: the common linear part and the exact cross-block row
translation differences. -/
def claim51892 {p : ℕ} {V : Type*} [Fintype V] [AddCommGroup V]
    [Module (ZMod p) V] (hp : Nat.Prime p)
    (X K N : Subgroup (Equiv.Perm (V × Fin 3))) : Prop :=
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  transitiveOn X ∧
    preservesThreeBlocks X ∧
    isThreeBlockKernel X K ∧
    N ≤ K ∧
    normalIn N X ∧
    isDiagonalTranslationGroup (p := p) N ∧
    primitiveAffineBlockAction (𝕜 := ZMod p) K →
      ∃ A : K → V ≃ₗ[ZMod p] V, ∃ b : K → Fin 3 → V,
        (∀ k : K, ∀ x : V, ∀ i : Fin 3,
          k.1 (x, i) = (A k x + b k i, i)) ∧
        commonLinearImageIrreducible A ∧
        (∀ k : K, ∀ i j : Fin 3, ∀ x : V,
          (diagonalTranslate (-b k i) (k.1 (x, j))).1 =
            A k x + (b k j - b k i) ∧
          (diagonalTranslate (-b k i) (k.1 (x, j))).2 = j)

end MathlibPlus.Open.Research
