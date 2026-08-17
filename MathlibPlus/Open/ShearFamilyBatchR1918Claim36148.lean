import Mathlib
import MathlibPlus.Open.ShearFamilyBatchR1918Claim36146

noncomputable section

namespace MathlibPlus.Open.ShearFamilyBatch

/-- Claim 36148: the exact planar shear construction gives unbounded metric and
centered-Gram fiber dimensions while the contact graph, point order, minimum
distance, and diameter are fixed at each order. -/
def allOrderUnboundedMetricFiberDimension_claim36148 : Prop :=
  ∀ B : ℕ, ∃ k : ℕ, B ≤ k ∧ 1 ≤ k ∧
    Fintype.card (Claim36146Vertex k) = 6 * k + 5 ∧
    (∀ a : Fin k → ℝ,
      claim36144_openBox k a →
        claim36146_family k a ∈ claim36146_fixedFiber k) ∧
    Module.finrank ℝ (claim36146_distanceFiberSpan k) ≥ k ∧
    Module.finrank ℝ (claim36146_gramFiberSpan k) ≥ k

end MathlibPlus.Open.ShearFamilyBatch
