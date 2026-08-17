import MathlibPlus.Open.Combinatorics.TreeAttachment

namespace MathlibPlus.Open.ResearchFormalizationD0083

open scoped BigOperators
open MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable section

private def oneLeOfThree {n : ℕ} (h : 3 ≤ n) : 1 ≤ n :=
  Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 2)) h

private def vertexDegree {m : ℕ} (C : UnlabelledTree m) (v : Vertex m) : ℕ :=
  Nat.card ((treeRepresentative C).1.neighborSet v)

private def secondAttachmentNeighborLoad {m : ℕ}
    (C : UnlabelledTree m) (v : Vertex m) : ℚ :=
  ∑ x : Vertex m,
    @ite ℚ ((treeRepresentative C).1.Adj v x)
      (Classical.propDecidable _)
      ((vertexDegree C x : ℚ) - 1) 0

private def secondAttachmentFeatureWeight {m : ℕ}
    (i : Fin 4) (x : RootedOccurrence m) : ℚ :=
  match i.1 with
  | 0 => 1
  | 1 => (vertexDegree x.1 x.2 : ℚ)
  | 2 => (Nat.choose (vertexDegree x.1 x.2) 2 : ℚ)
  | 3 => secondAttachmentNeighborLoad x.1 x.2
  | _ => 0

private def secondAttachmentMomentVector {m : ℕ}
    (i : Fin 4) (C : UnlabelledTree m) : RootedCardSpace m :=
  ∑ v : Vertex m,
    secondAttachmentFeatureWeight i (C, v) • rootedBasis C v

private def secondAttachmentMomentSpace (n : ℕ) :
    Submodule ℚ (RootedCardSpace (n - 1)) :=
  Submodule.span ℚ (Set.range fun p : Fin 4 × UnlabelledTree (n - 1) =>
    secondAttachmentMomentVector p.1 p.2)

private def secondAttachmentExchangeSpace (n : ℕ) (h : 1 ≤ n) :
    Submodule ℚ (RootedCardSpace (n - 1)) :=
  Submodule.span ℚ {z |
    ∃ x y : RootedOccurrence (n - 1),
      attachmentMapAt n h x = attachmentMapAt n h y ∧
        z = rootedBasis x.1 x.2 - rootedBasis y.1 y.2}

/-- Claim 5146: the exact four second-attachment feature channels,
`1`, degree, `binom(degree,2)`, and the sum of neighbour degrees minus one,
give zero global rooted-card presentation defect for every target size `n≥3`.
The rooted-card carrier is indexed by `(n-1)`-vertex cards and the target by
`n`-vertex trees. -/
def claim5146 : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n),
      let h : 1 ≤ n := oneLeOfThree hn
      let momentSpace := secondAttachmentMomentSpace n
      let exchangeSpace := secondAttachmentExchangeSpace n h
      ∀ x : RootedCardSpace (n - 1) ⧸ (momentSpace ⊔ exchangeSpace),
        x = 0

end

end MathlibPlus.Open.ResearchFormalizationD0083
