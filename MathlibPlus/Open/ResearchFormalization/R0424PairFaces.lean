import MathlibPlus.Open.Research.UnionClosedBatch

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0424PairFaces

noncomputable section

open MathlibPlus.Open.Research

private def sourceRow {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  A.filter (fun G => x ∈ G)

private def pairTop {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α)) : Finset α :=
  familyUnion (joinFamilies A B)

private def nonTopOutputRow {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (joinFamilies A B).filter (fun E => x ∈ E ∧ E ≠ pairTop A B)

private def pairFaceCode {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α)) (G : Finset α) : Finset (Finset α) :=
  (B.image (fun H => G ∪ H)).filter (fun E => E ≠ pairTop A B)

/-- Claim 21191: the pair join, its top, the source `x`-row, and the
non-top `x`-containing output row are the stated finite-set carriers, with
`p_i(x)` and `r_ij(x)` their exact cardinalities. -/
def pairFaceOutputFamilyAndNonTopCount_claim21191 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (A_i A_j : Finset (Finset α)) (x : α),
    A_i.Nonempty → A_j.Nonempty →
      let Q_ij := pairTop A_i A_j
      let X_i := sourceRow A_i x
      let E_ij := nonTopOutputRow A_i A_j x
      let p_i := X_i.card
      let r_ij := E_ij.card
      (joinFamilies A_i A_j).Nonempty ∧
        Q_ij = familyUnion (joinFamilies A_i A_j) ∧
        p_i = (A_i.filter (fun G => x ∈ G)).card ∧
        r_ij =
          ((joinFamilies A_i A_j).filter
            (fun E => x ∈ E ∧ E ≠ familyUnion (joinFamilies A_i A_j))).card

/-- Claim 21192: the pair-face code consists exactly of the non-top outputs
`G ∪ H` from the second factor and is contained in the named non-top output
row. -/
def pairFaceIntersectionCode_claim21192 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (A_i A_j : Finset (Finset α)) (x : α) (G : Finset α),
    A_i.Nonempty → A_j.Nonempty → G ∈ sourceRow A_i x →
      pairFaceCode A_i A_j G ⊆ nonTopOutputRow A_i A_j x

/-- Claim 21194: with the nonempty second factor and its empty total
intersection, the pair-face code is injective on the `x`-containing row. -/
def pairFaceCodeInjective_claim21194 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (A_i A_j : Finset (Finset α)) (x : α),
    A_i.Nonempty → A_j.Nonempty →
    commonIntersection A_j = ∅ →
      ∀ G G' : Finset α,
        G ∈ sourceRow A_i x → G' ∈ sourceRow A_i x →
        pairFaceCode A_i A_j G = pairFaceCode A_i A_j G' → G = G'

/-- Claim 21195: the exact subset-capacity bound obtained from the injective
pair-face code. -/
def exponentialPairFaceCapacityBound_claim21195 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (A_i A_j : Finset (Finset α)) (x : α),
    A_i.Nonempty → A_j.Nonempty →
    commonIntersection A_j = ∅ →
      (sourceRow A_i x).card ≤
        2 ^ (nonTopOutputRow A_i A_j x).card

end

end MathlibPlus.Open.ResearchFormalization.R0424PairFaces
