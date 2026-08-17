import Mathlib
import MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.LeafOperatorClaims19629_19633

open scoped BigOperators
open MathlibPlus.Open.TreeSpectral

noncomputable section

private def loweringMap (n : ℕ) :
    TreeSpace (n + 1) →ₗ[ℚ] TreeSpace n := by
  have h : (n + 1) - 1 = n := by omega
  exact (transportTreeSpace h).comp (leafDeletion (n + 1))

private def previousRaisingMap (n : ℕ) (h : 1 ≤ n) :
    TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace (Nat.sub_add_cancel h)).comp (graft (n - 1))

private def eMap (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace (n + 1) :=
  graft n

private def fMap (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace (n - 1) :=
  (-2 : ℚ) • leafDeletion n

private def fNextMap (n : ℕ) :
    TreeSpace (n + 1) →ₗ[ℚ] TreeSpace n :=
  (-2 : ℚ) • loweringMap n

private def hMap (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace n :=
  (2 * (n : ℚ)) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)

private def internalDirectSum {n : ℕ}
    (U : Fin (n + 1) → Submodule ℚ (TreeSpace n)) : Prop :=
  ∀ v : TreeSpace n, ∃! u : ∀ k, U k,
    (∑ k : Fin (n + 1), (u k : TreeSpace n)) = v

private def graftingDepthSubmodule (n : ℕ) (k : Fin (n + 1)) :
    Submodule ℚ (TreeSpace n) :=
  MathlibPlus.Open.TreeSpectral.tower n k.1 (Nat.le_of_lt_succ k.2)

/-- Claim 19629: the graded leaf commutator is n times the identity on every
specified degree n ≥ 2. -/
def gradedLeafCommutator_claim19629 : Prop :=
  ∀ n : ℕ, ∀ hn : 2 ≤ n,
    let h : 1 ≤ n := by omega
    (loweringMap n).comp (graft n) -
        (previousRaisingMap n h).comp (leafDeletion n) =
      (n : ℚ) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)

/-- Claim 19630: the degree-shifted leaf maps e=G, f=-2L and h=2N satisfy
all three sl₂ commutator identities on degrees n ≥ 2. -/
def leafOperatorsFormSL2Triple_claim19630 : Prop :=
  ∀ n : ℕ, ∀ hn : 2 ≤ n,
    (let h : 1 ≤ n := by omega;
      (previousRaisingMap n h).comp (fMap n) -
          (fNextMap n).comp (eMap n) = hMap n) ∧
      ((hMap (n + 1)).comp (eMap n) -
          (eMap n).comp (hMap n) = (2 : ℚ) • eMap n) ∧
      ((hMap (n - 1)).comp (fMap n) -
          (fMap n).comp (hMap n) = (-2 : ℚ) • fMap n)

/-- Claim 19632: leaf deletion is surjective and leaf grafting is injective in
every degree represented by the graded tree spaces. -/
def leafOperatorsSurjectiveInjective_claim19632 : Prop :=
  (∀ n : ℕ, Function.Surjective (loweringMap n)) ∧
    (∀ n : ℕ, Function.Injective (graft n))

/-- Claim 19633: the subspaces obtained by k successive graftings from the
kernel of the lowering map in birth degree n-k form a canonical internal direct
sum of TreeSpace n. -/
def graftingDepthDecomposition_claim19633 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    internalDirectSum (graftingDepthSubmodule n)

end

end MathlibPlus.Open.ResearchFormalization.LeafOperatorClaims19629_19633
