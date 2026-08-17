import Mathlib
import MathlibPlus.Open.TreeSpectral

open scoped BigOperators
open MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.R0335

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev AttachmentSource (n : ℕ) := (TreeClass (n - 1) × Fin 4) →₀ ℚ
abbrev AttachmentTarget (n : ℕ) := TreeSpace n

/-- The degree of a vertex in a graph on the finite vertex set `Fin n`. -/
noncomputable def treeDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The leaf condition in a representative of an unlabelled tree. -/
noncomputable def representativeIsLeaf {n : ℕ} (T : TreeClass n) (ell : Fin n) : Prop :=
  treeDegree (Quotient.out T).1 ell = 1

/-- The card obtained by deleting a specified leaf is compared with a card-tree representative. -/
noncomputable def cardDeletionIsomorphism {n : ℕ}
    (C : TreeClass (n - 1)) (T : TreeClass n) (ell : Fin n) : Prop :=
  GraphIso
    ((Quotient.out T).1.induce {v : Fin n | v ≠ ell})
    (Quotient.out C).1

/-- The neighbour degree contribution of a leaf, written as a finite sum over its unique neighbour. -/
noncomputable def attachmentDegree {n : ℕ}
    (T : TreeClass n) (ell : Fin n) : ℕ :=
  ∑ v : Fin n,
    if (Quotient.out T).1.Adj ell v then
      treeDegree (Quotient.out T).1 v - 1
    else 0

/-- The two-step contribution at the neighbour of a leaf. -/
noncomputable def attachmentTwoStepWeight {n : ℕ}
    (T : TreeClass n) (ell : Fin n) : ℕ :=
  ∑ v : Fin n,
    if (Quotient.out T).1.Adj ell v then
      ∑ x : Fin n,
        if (Quotient.out T).1.Adj v x ∧ x ≠ ell then
          treeDegree (Quotient.out T).1 x - 1
        else 0
    else 0

/-- The four weights indexed by the four channels of the second attachment jet. -/
noncomputable def attachmentChannelWeight {n : ℕ}
    (k : Fin 4) (T : TreeClass n) (ell : Fin n) : ℕ :=
  if k.val = 0 then 1
  else if k.val = 1 then attachmentDegree T ell
  else if k.val = 2 then Nat.choose (attachmentDegree T ell) 2
  else attachmentTwoStepWeight T ell

/-- The four exact leaf-attachment channels, indexed by card and target tree. -/
noncomputable def attachmentChannel {n : ℕ}
    (k : Fin 4) (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  ∑ ell : Fin n,
    if representativeIsLeaf T ell ∧ cardDeletionIsomorphism C T ell then
      attachmentChannelWeight k T ell
    else 0

noncomputable def a₀ {n : ℕ} (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  attachmentChannel 0 C T

noncomputable def a₁ {n : ℕ} (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  attachmentChannel 1 C T

noncomputable def a₂Star {n : ℕ} (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  attachmentChannel 2 C T

noncomputable def a₂Path {n : ℕ} (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  attachmentChannel 3 C T

/-- The integer matrix whose rows are the four card channels and whose columns are target trees. -/
noncomputable def attachmentMatrixInt (n : ℕ) :
    Matrix (TreeClass (n - 1) × Fin 4) (TreeClass n) ℤ :=
  fun r T => attachmentChannel r.2 r.1 T

noncomputable def attachmentMatrixQ (n : ℕ) :
    Matrix (TreeClass (n - 1) × Fin 4) (TreeClass n) ℚ :=
  fun r T => attachmentMatrixInt n r T

/-- Vertices for a graft of a card representative, with a fresh one-vertex summand. -/
abbrev GraftVertices (n : ℕ) := Fin (n - 1) ⊕ Fin 1

/-- Graft a new leaf to a card representative at a specified card vertex. -/
noncomputable def cardGraftGraph {n : ℕ}
    (C : TreeGraph (n - 1)) (v : Fin (n - 1)) : SimpleGraph (GraftVertices n) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl a, Sum.inl b => C.1.Adj a b
    | Sum.inl a, Sum.inr _ => a = v
    | Sum.inr _, Sum.inl b => v = b
    | Sum.inr _, Sum.inr _ => False)

noncomputable def cardNeighborWeight {n : ℕ}
    (C : TreeGraph (n - 1)) (v : Fin (n - 1)) : ℕ :=
  ∑ x : Fin (n - 1),
    if C.1.Adj v x then treeDegree C.1 x - 1 else 0

noncomputable def graftWeight {n : ℕ}
    (k : Fin 4) (C : TreeGraph (n - 1)) (v : Fin (n - 1)) : ℕ :=
  if k.val = 0 then 1
  else if k.val = 1 then treeDegree C.1 v
  else if k.val = 2 then Nat.choose (treeDegree C.1 v) 2
  else cardNeighborWeight C v

/-- The post-automorphism-gauge weighted grafting action on a card basis vector. -/
noncomputable def weightedGraftBasis (n : ℕ) (k : Fin 4)
    (C : TreeClass (n - 1)) : TreeSpace n :=
  ∑ v : Fin (n - 1),
    ∑ T : TreeClass n,
      Finsupp.single T
        (if GraphIso (cardGraftGraph (Quotient.out C) v) (Quotient.out T).1 then
          (graftWeight k (Quotient.out C) v : ℚ)
        else 0)

noncomputable def weightedGraft (n : ℕ) (k : Fin 4) :
    TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  linearExtension (weightedGraftBasis n k)

noncomputable def G₀ (n : ℕ) : TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  weightedGraft n 0

noncomputable def G₁ (n : ℕ) : TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  weightedGraft n 1

noncomputable def G₂Star (n : ℕ) : TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  weightedGraft n 2

noncomputable def G₂Path (n : ℕ) : TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  weightedGraft n 3

noncomputable def jointGraftingImageSum (n : ℕ) : Submodule ℚ (TreeSpace n) :=
  LinearMap.range (G₀ n) ⊔ LinearMap.range (G₁ n) ⊔
    LinearMap.range (G₂Star n) ⊔ LinearMap.range (G₂Path n)

noncomputable def attachmentFullColumnRank (n : ℕ) : Prop :=
  Matrix.rank (attachmentMatrixQ n) = Fintype.card (TreeClass n)

/-- Claim 20033: full column rank is joint grafting surjectivity. -/
def claim20033 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (attachmentFullColumnRank n ↔ jointGraftingImageSum n = ⊤)

noncomputable def attachmentMatrixRankQ (n : ℕ) : ℕ :=
  Matrix.rank (attachmentMatrixQ n)

noncomputable def attachmentMatrixModPrime (n : ℕ) :
    Matrix (TreeClass (n - 1) × Fin 4) (TreeClass n) (ZMod 1000003) :=
  fun r T => attachmentMatrixInt n r T

noncomputable def attachmentMatrixRankModPrime (n : ℕ) : ℕ :=
  Matrix.rank (attachmentMatrixModPrime n)

noncomputable def rankColumnSequenceThroughTwelve : List (ℕ × ℕ) :=
  [ (attachmentMatrixRankQ 3, Fintype.card (TreeClass 3)),
    (attachmentMatrixRankQ 4, Fintype.card (TreeClass 4)),
    (attachmentMatrixRankQ 5, Fintype.card (TreeClass 5)),
    (attachmentMatrixRankQ 6, Fintype.card (TreeClass 6)),
    (attachmentMatrixRankQ 7, Fintype.card (TreeClass 7)),
    (attachmentMatrixRankQ 8, Fintype.card (TreeClass 8)),
    (attachmentMatrixRankQ 9, Fintype.card (TreeClass 9)),
    (attachmentMatrixRankQ 10, Fintype.card (TreeClass 10)),
    (attachmentMatrixRankQ 11, Fintype.card (TreeClass 11)),
    (attachmentMatrixRankQ 12, Fintype.card (TreeClass 12)) ]

/-- Claim 20035: the displayed rational and modular ranks through order twelve. -/
def claim20035 : Prop :=
  (∀ n : ℕ, 3 ≤ n → n ≤ 12 →
    attachmentMatrixRankQ n = Fintype.card (TreeClass n)) ∧
  rankColumnSequenceThroughTwelve =
    [ (1, 1), (2, 2), (3, 3), (6, 6), (11, 11),
      (23, 23), (47, 47), (106, 106), (235, 235), (551, 551) ] ∧
  ((∀ n : ℕ, 3 ≤ n → n ≤ 12 →
      attachmentMatrixRankModPrime n = Fintype.card (TreeClass n)) →
    ∀ n : ℕ, 3 ≤ n → n ≤ 12 →
      attachmentMatrixRankQ n = Fintype.card (TreeClass n))

noncomputable def M18 :
    Matrix (TreeClass 17 × Fin 4) (TreeClass 18) ℤ :=
  attachmentMatrixInt 18

/-- Claim 20038: the order-eighteen integer matrix has the stated dimensions. -/
def claim20038 : Prop :=
  Fintype.card (TreeClass 17 × Fin 4) = 194516 ∧
  Fintype.card (TreeClass 18) = 123867 ∧
  ∀ r T, M18 r T = (attachmentChannel r.2 r.1 T : ℤ)

noncomputable def attachmentMapBasis (n : ℕ)
    (r : TreeClass (n - 1) × Fin 4) : TreeSpace n :=
  weightedGraftBasis n r.2 r.1

noncomputable def attachmentMap (n : ℕ) :
    AttachmentSource n →ₗ[ℚ] AttachmentTarget n :=
  linearExtension (attachmentMapBasis n)

noncomputable def loweringBasis (n : ℕ) (k : Fin 4)
    (T : TreeClass n) : TreeSpace (n - 1) :=
  ∑ C : TreeClass (n - 1),
    Finsupp.single C (attachmentMatrixQ n (C, k) T)

noncomputable def adjointLowering (n : ℕ) (k : Fin 4) :
    TreeSpace n →ₗ[ℚ] TreeSpace (n - 1) :=
  linearExtension (loweringBasis n k)

noncomputable def commonAdjointLoweringKernelZero (n : ℕ) : Prop :=
  ∀ x : TreeSpace n,
    (∀ k : Fin 4, adjointLowering n k x = 0) → x = 0

/-- Claim 20043: target rank is the reconstruction condition, not source-row injectivity. -/
def claim20043 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (Function.Surjective (attachmentMap n) ↔
      commonAdjointLoweringKernelZero n) ∧
    (attachmentFullColumnRank n ↔ Function.Surjective (attachmentMap n))

end

end MathlibPlus.Open.ResearchFormalization.R0335
