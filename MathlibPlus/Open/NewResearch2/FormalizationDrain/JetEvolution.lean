import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain.JetEvolution

noncomputable section

private def rankPartition (r : ℕ) (part : YoungDiagram) : Prop :=
  part.colLen 0 ≤ r

private def youngCover (part μ : YoungDiagram) : Prop :=
  part ≤ μ ∧ μ.card = part.card + 1

private def rankedYoungCover (r : ℕ) (part μ : YoungDiagram) : Prop :=
  rankPartition r part ∧ rankPartition r μ ∧ youngCover part μ

private noncomputable def addCellDiagram
    (part : YoungDiagram) (p : ℕ × ℕ) : YoungDiagram := by
  classical
  by_cases h : IsLowerSet ((insert p part.cells : Finset (ℕ × ℕ)) : Set (ℕ × ℕ))
  · exact { cells := insert p part.cells, isLowerSet := h }
  · exact ⊥

private noncomputable def coverFinset
    (r : ℕ) (part : YoungDiagram) : Finset YoungDiagram := by
  classical
  let candidates :=
    (Finset.product (Finset.range (r + 1))
      (Finset.range (part.rowLen 0 + 1))).image (addCellDiagram part)
  exact candidates.filter (rankedYoungCover r part)

private def jetIndex (r : ℕ) (part : YoungDiagram) (j : Fin r) : ℕ :=
  j.1 + part.rowLen (r - 1 - j.1)

private noncomputable def exteriorPacket
    (c : ℕ → ℝ → ℕ → ℝ) (r : ℕ) (part : YoungDiagram)
    (t : ℝ) (I : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r => c (jetIndex r part j) t (I i))

private def gaugeNormalizedJet (c : ℕ → ℝ → ℕ → ℝ) : Prop :=
  ∀ j : ℕ, ∀ t : ℝ, ∀ n : ℕ,
    HasDerivAt (fun s : ℝ => c j s n) (c (j + 1) t n) t

/-- Claim 18256: the exterior minors of the gauge-normalized jet flag are
indexed by rank-compatible Young diagrams, and differentiating a packet
raises one exterior index, with one unit coefficient for every one-box cover. -/
def claim18256_youngBoxRaisingEvolution
    (c : ℕ → ℝ → ℕ → ℝ) : Prop :=
  gaugeNormalizedJet c →
    ∀ (r : ℕ) (part : YoungDiagram) (t : ℝ), rankPartition r part →
      ∀ I : Fin r → ℕ,
        HasDerivAt
          (fun s : ℝ => exteriorPacket c r part s I)
          (∑ μ ∈ coverFinset r part, exteriorPacket c r μ t I) t

private noncomputable def allCoverFinset (part : YoungDiagram) : Finset YoungDiagram :=
  coverFinset (part.colLen 0 + 1) part

private noncomputable def youngBoxRaisingGenerator
    (part μ : YoungDiagram) : ℝ := by
  classical
  exact if youngCover part μ then 1 else 0

private def generatorAction
    (u : ℝ → YoungDiagram → ℝ) (t : ℝ) (part : YoungDiagram) : ℝ :=
  ∑ μ ∈ allCoverFinset part, u t μ

private def youngFlowSolution (u : ℝ → YoungDiagram → ℝ) : Prop :=
  ∀ (part : YoungDiagram) (t : ℝ),
    HasDerivAt (fun s : ℝ => u s part) (generatorAction u t part) t

private def coordinatewiseNonnegative
    (u : ℝ → YoungDiagram → ℝ) (t : ℝ) : Prop :=
  ∀ part : YoungDiagram, 0 ≤ u t part

/-- Claim 18257: the Young one-box generator has unit entries precisely on
covers and zero on every other off-diagonal entry; its forward solutions
preserve the coordinatewise nonnegative cone. -/
def claim18257_youngBoxRaisingGeneratorMetzler : Prop := by
  classical
  exact
    (∀ part μ : YoungDiagram, part ≠ μ →
      youngBoxRaisingGenerator part μ = if youngCover part μ then 1 else 0) ∧
    (∀ part μ : YoungDiagram, part ≠ μ →
      0 ≤ youngBoxRaisingGenerator part μ) ∧
    (∀ u : ℝ → YoungDiagram → ℝ,
      youngFlowSolution u → coordinatewiseNonnegative u 0 →
        ∀ t : ℝ, 0 ≤ t → coordinatewiseNonnegative u t)

end
end MathlibPlus.Open.NewResearch2.FormalizationDrain.JetEvolution
