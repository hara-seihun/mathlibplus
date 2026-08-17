import Mathlib
import MathlibPlus.Open.Combinatorics.TreeAttachment

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.D0083Claim5141

open MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable def momentVector
    (n : ℕ) (Feature : Type*)
    (weight : Feature → RootedOccurrence (n - 1) → ℚ)
    (f : Feature) (C : UnlabelledTree (n - 1)) :
    RootedCardSpace (n - 1) :=
  ∑ v : Vertex (n - 1),
    weight f (C, v) • rootedBasis C v

noncomputable def momentSpace
    (n : ℕ) (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ) :
    Submodule ℚ (RootedCardSpace (n - 1)) :=
  Submodule.span ℚ
    (Set.range fun p : Feature × UnlabelledTree (n - 1) =>
      momentVector n Feature weight p.1 p.2)

noncomputable def globalExchangeSpace
    (n : ℕ) (h : 1 ≤ n) :
    Submodule ℚ (RootedCardSpace (n - 1)) :=
  Submodule.span ℚ {
    z | ∃ x y : RootedOccurrence (n - 1),
      attachmentMapAt n h x = attachmentMapAt n h y ∧
        z = rootedBasis x.1 x.2 - rootedBasis y.1 y.2
  }

abbrev attachmentDefect
    (n : ℕ) (h : 1 ≤ n) (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ) : Type :=
  RootedCardSpace (n - 1) ⧸
    (momentSpace n Feature weight ⊔ globalExchangeSpace n h)

noncomputable def weightedGraftingMap
    (n : ℕ) (h : 1 ≤ n) (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ) :
    (Feature × UnlabelledTree (n - 1) →₀ ℚ) →ₗ[ℚ] TreeSpace n :=
  Finsupp.linearCombination ℚ (fun p : Feature × UnlabelledTree (n - 1) =>
    attachmentLinearizationAt n h
      (momentVector n Feature weight p.1 p.2))

abbrev weightedGraftingCokernel
    (n : ℕ) (h : 1 ≤ n) (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ) : Type :=
  TreeSpace n ⧸ LinearMap.range (weightedGraftingMap n h Feature weight)

def automorphismInvariantWeight
    (n : ℕ) (Feature : Type*)
    (weight : Feature → RootedOccurrence (n - 1) → ℚ) : Prop :=
  ∀ f : Feature, ∀ C : UnlabelledTree (n - 1),
    ∀ e : (treeRepresentative C).1 ≃g (treeRepresentative C).1,
      ∀ v : Vertex (n - 1),
        weight f (C, e v) = weight f (C, v)

def canonicalDefectCokernelMap
    (n : ℕ) (h : 1 ≤ n) (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ)
    (q : attachmentDefect n h Feature weight →ₗ[ℚ]
      weightedGraftingCokernel n h Feature weight) : Prop :=
  ∀ x : RootedCardSpace (n - 1),
    q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (attachmentLinearizationAt n h x)

/-- Claim 5141: after surjective attachment, the actual rooted-card defect is
canonically equivalent to the cokernel of the actual weighted grafting map;
the defect is zero exactly when that weighted family is surjective. -/
def claim5141 : Prop :=
  ∀ (n : ℕ), ∀ hn : 2 ≤ n,
    let h : 1 ≤ n := Nat.le_trans (by norm_num) hn
    ∀ (Feature : Type*) [Fintype Feature]
      (weight : Feature → RootedOccurrence (n - 1) → ℚ),
      automorphismInvariantWeight n Feature weight →
      Function.Surjective (attachmentLinearizationAt n h) →
      globalExchangeSpace n h = LinearMap.ker (attachmentLinearizationAt n h) ∧
        LinearMap.range (weightedGraftingMap n h Feature weight) =
          Submodule.map (attachmentLinearizationAt n h)
            (momentSpace n Feature weight) ∧
        (∃! q : attachmentDefect n h Feature weight →ₗ[ℚ]
            weightedGraftingCokernel n h Feature weight,
          canonicalDefectCokernelMap n h Feature weight q ∧
            Function.Bijective q) ∧
        ((∀ x : attachmentDefect n h Feature weight, x = 0) ↔
          Function.Surjective (weightedGraftingMap n h Feature weight))

end MathlibPlus.Open.ResearchFormalization.D0083Claim5141
