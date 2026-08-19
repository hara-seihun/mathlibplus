import MathlibPlus.Open.ResearchFormalization.O0352

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.C0291Claim4081

open MathlibPlus.Open.ResearchFormalization.O0352
open MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus

/-- A column of the exact tree-level leaf-deck block. -/
def leafDeckColumn (n : ℕ) (T : TreeColumn n) : LeafRow15580 n → ℚ :=
  fun μ => leafDeckMatrix15580 n μ T

/-- The displayed tree-count triple at an order. -/
def treeCountTriple (n a b s : ℕ) : Prop :=
  treeCount15580 n = a ∧
    treeCount15580 (n - 1) = b ∧
      treeCount15580 n - treeCount15580 (n - 1) = s

/-- The exact order-five-through-fourteen census in Claim 4081. -/
def table4081 : Prop :=
  treeCountTriple 5 3 2 1 ∧
    treeCountTriple 6 6 3 3 ∧
    treeCountTriple 7 11 6 5 ∧
    treeCountTriple 8 23 11 12 ∧
    treeCountTriple 9 47 23 24 ∧
    treeCountTriple 10 106 47 59 ∧
    treeCountTriple 11 235 106 129 ∧
    treeCountTriple 12 551 235 316 ∧
    treeCountTriple 13 1301 551 750 ∧
    treeCountTriple 14 3159 1301 1858

/-- Claim 4081: pairwise-distinct tree leaf-deck columns attain the exact
rank shortfall and have the displayed order-five-through-fourteen values. -/
def claim4081_pairwiseSeparationExactRankShortfall : Prop :=
  table4081 ∧
    ∀ (n : ℕ), 5 ≤ n →
      letI : Fintype (TreeColumn n) := Fintype.ofFinite _
      Pairwise (fun T U : TreeColumn n =>
          leafDeckColumn n T ≠ leafDeckColumn n U) ∧
        Matrix.rank (leafDeckMatrix15580 n) = treeCount15580 (n - 1) ∧
        treeCount15580 n - Matrix.rank (leafDeckMatrix15580 n) =
          treeCount15580 n - treeCount15580 (n - 1)

end MathlibPlus.Open.ResearchFormalization.C0291Claim4081

end
