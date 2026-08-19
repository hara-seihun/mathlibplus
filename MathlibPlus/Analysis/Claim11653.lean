import Mathlib

namespace MathlibPlus.Analysis.Claim11653

open MeasureTheory

/-- The physical positive kernel `k_m` supplied by the cutoff packet, with
its exact base and second-derivative recurrence retained. -/
noncomputable def physicalKernel11653 : ℕ → ℝ → ℝ :=
  Nat.rec
    (fun d : ℝ => 1 / (2 * Real.cosh d))
    (fun j f d => f d - iteratedDeriv 2 f d /
      (4 * ((j + 1 : ℕ) : ℝ) ^ 2))

/-- The source order-three cutoff object, defined from the physical kernel
rather than minted as its displayed rational value. -/
noncomputable def orderThreeCutoff : ℝ :=
  (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1,
    r * physicalKernel11653 3 (Real.log r)

/-- Claim 11653: the source-defined order-three cutoff evaluates to the
exact displayed value. -/
def orderThreeCutoff_eq : Prop :=
  orderThreeCutoff = (211 : ℝ) / 1536

end MathlibPlus.Analysis.Claim11653
