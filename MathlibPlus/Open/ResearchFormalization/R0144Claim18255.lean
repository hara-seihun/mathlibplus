import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0144Claim18255

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

private def rankPartition (r : ℕ) (part : YoungDiagram) : Prop :=
  part.colLen 0 ≤ r

private def youngCover (part μ : YoungDiagram) : Prop :=
  part ≤ μ ∧ μ.card = part.card + 1

private def rankedYoungCover (r : ℕ) (part μ : YoungDiagram) : Prop :=
  rankPartition r part ∧ rankPartition r μ ∧ youngCover part μ

private noncomputable def addCellDiagram
    (part : YoungDiagram) (p : ℕ × ℕ) : YoungDiagram :=
  if h : IsLowerSet ((insert p part.cells : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) then
    { cells := insert p part.cells, isLowerSet := h }
  else ⊥

private noncomputable def coverFinset
    (r : ℕ) (part : YoungDiagram) : Finset YoungDiagram :=
  let candidates :=
    (Finset.product (Finset.range (r + 1))
      (Finset.range (part.rowLen 0 + 1))).image (addCellDiagram part)
  candidates.filter (rankedYoungCover r part)

private def jetIndex (r : ℕ) (part : YoungDiagram) (j : Fin r) : ℕ :=
  j.1 + part.rowLen (r - 1 - j.1)

private noncomputable def exteriorPacket
    (c : ℕ → ℝ → ℕ → ℝ) (r : ℕ) (part : YoungDiagram)
    (t : ℝ) (I : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r => c (jetIndex r part j) t (I i))

private noncomputable def exteriorPacketFamily
    (c : ℕ → ℝ → ℕ → ℝ) (r : ℕ) (t : ℝ) (I : Fin r → ℕ) :
    YoungDiagram → ℝ :=
  fun part => exteriorPacket c r part t I

private def gaugeNormalizedJet (c : ℕ → ℝ → ℕ → ℝ) : Prop :=
  ∀ j : ℕ, ∀ t : ℝ, ∀ n : ℕ,
    HasDerivAt (fun s : ℝ => c j s n) (c (j + 1) t n) t

private def oneBoxRaisesOneExteriorIndex
    (r : ℕ) (part μ : YoungDiagram) : Prop :=
  rankedYoungCover r part μ →
    ∃ j : Fin r,
      jetIndex r μ j = jetIndex r part j + 1 ∧
        ∀ k : Fin r, k ≠ j → jetIndex r μ k = jetIndex r part k

/-- Claim 18255: the gauged jet minors form the concrete partition-indexed
    packet family, and each rank-compatible one-box cover raises exactly one
    exterior jet index by one. -/
def claim18255_exteriorPacketsIndexedByPartitions
    (c : ℕ → ℝ → ℕ → ℝ) : Prop :=
  gaugeNormalizedJet c →
    ∀ (r : ℕ) (t : ℝ) (I : Fin r → ℕ),
      (∀ part : YoungDiagram,
        exteriorPacketFamily c r t I part =
          Matrix.det (fun i j : Fin r =>
            c (jetIndex r part j) t (I i))) ∧
      (∀ part μ : YoungDiagram,
        oneBoxRaisesOneExteriorIndex r part μ)

end

end MathlibPlus.Open.ResearchFormalization.R0144Claim18255
