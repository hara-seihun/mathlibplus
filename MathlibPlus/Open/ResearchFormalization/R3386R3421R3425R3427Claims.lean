import Mathlib
import MathlibPlus.Open.GraphTheory.PinnedGoodBatch
import MathlibPlus.Open.Probability.ResearchBatch
import MathlibPlus.LinearAlgebra.RankTwoIntervalReflection

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim46728

noncomputable section

private def extensionRatio46728 {α : ℕ}
    (a : Fin (α + 1) → ℝ) (k : Fin α) : ℝ :=
  ((k.val + 1 : ℕ) : ℝ) * a k.succ / a k.castSucc

private def shiftedExtensionRatio46728 {α : ℕ}
    (a : Fin (α + 1) → ℝ) (k : Fin α) : ℝ :=
  extensionRatio46728 a k - ((k.val + 1 : ℕ) : ℝ)

/-- Claim 46728: the ordered-GSB local inequality is exactly equivalent to
monotonicity of the shifted extension ratio on its valid k≥1 range. -/
def orderedGSBInequalityEquivalence_claim46728 : Prop :=
  ∀ (α : ℕ) (a : Fin (α + 1) → ℝ),
    (∀ i, 0 < a i) →
      ∀ k : Fin (α + 1),
        (hlast : k ≠ Fin.last α) → (hzero : k ≠ 0) →
        let kk : Fin α := k.castPred hlast
        let kp : Fin α := k.pred hzero
        (extensionRatio46728 a kk ≤ extensionRatio46728 a kp + 1 ↔
          shiftedExtensionRatio46728 a kk ≤
            shiftedExtensionRatio46728 a kp)

end
end MathlibPlus.Algebra.Claim46728

namespace MathlibPlus.Open.GraphTheory

open MathlibPlus.Open.GraphTheory.PinnedGood

/-- Claim 46759: exact degree and conditional codegree bounds for a
(5,5)-good graph on the 43-element carrier.  The non-edge bound explicitly
requires distinct endpoints, avoiding the irreflexive diagonal. -/
def claim46759_degreeAndCodegreeBounds : Prop :=
  ∀ G : SimpleGraph (Fin 43),
    IsGood55 G →
      (∀ v : Fin 43,
        18 ≤ (G.neighborSet v).ncard ∧
          (G.neighborSet v).ncard ≤ 24) ∧
        (∀ ⦃u v : Fin 43⦄, G.Adj u v →
          (G.commonNeighbors u v).ncard ≤ 13) ∧
          (∀ ⦃u v : Fin 43⦄, u ≠ v → ¬ G.Adj u v →
            ((Gᶜ).commonNeighbors u v).ncard ≤ 13)

end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.Open.Probability.ResearchBatch

noncomputable section

private def signReal46769 (b : Bool) : ℝ :=
  if b then 1 else -1

private def sharedSelectorTarget46769 (n : ℕ) : Cube (2 + n) → ℝ :=
  fun x =>
    (∑ i : Fin n,
      if x (Fin.natAdd 2 i) then signReal46769 (x 1)
      else signReal46769 (x 0)) / (n : ℝ)

private def selectorChain46769 (n : ℕ) : QueryTree (2 + n) :=
  (List.ofFn (fun i : Fin n => Fin.natAdd 2 i)).foldr
    (fun i t => .node i t t) .leaf

/-- The legal policy that queries Y₋, then Y₊, and queries every selector only
on the two branches where the shared signs disagree. -/
def directSharedSelectorPolicy46769 (n : ℕ) : QueryTree (2 + n) :=
  .node 0
    (.node 1 .leaf (selectorChain46769 n))
    (.node 1 (selectorChain46769 n) .leaf)

/-- Claim 46769: the policy and Boolean-sign probability model are connected
through the exact finite cube, completion, and root-inclusive posterior
variance area; its area is 1+5/(4n), below 2 for n≥2 and equal to 5/4 at n=5. -/
def legalPolicyArea_lt_two : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    let μ := sharedSelectorTarget46769 n
    let policy := directSharedSelectorPolicy46769 n
    valid policy ∧
      complete μ policy ∧
        policyArea μ policy = 1 + 5 / (4 * (n : ℝ)) ∧
          policyArea μ policy < 2 ∧
            (n = 5 → policyArea μ policy = 5 / 4)

end
end MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.LinearAlgebra.RankTwoIntervalReflection

/-- Claim 46789: the displayed repeated interval-reflection block has
 determinant -4. -/
def rankTwoIntervalReflection_det_claim46789 : Prop :=
  Matrix.det rankTwoIntervalReflection = (-4 : ℝ)

end MathlibPlus.LinearAlgebra.RankTwoIntervalReflection
