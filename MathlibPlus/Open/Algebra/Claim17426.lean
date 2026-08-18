import Mathlib
import MathlibPlus.Open.Algebra.Claim17425_17428

open scoped BigOperators
open MathlibPlus.Algebra.Claim17423
open MathlibPlus.Open.Algebra.Claim17425_17428

namespace MathlibPlus.Open.Algebra.Claim17426

noncomputable section

/-- The maximum of the absolute prefix charges on all path vertices. -/
def prefixInfinityNorm {N : ℕ} (e : VertexChain ℝ N) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin (N + 1))) Finset.univ_nonempty
    (fun k => |prefixSum e k|)

/-- Claim 17426: on every zero-mass finite path event chain, the canonical
filling infinity norm is exactly the maximum absolute prefix charge. -/
def claim17426 : Prop :=
  ∀ (N : ℕ) (e : VertexChain ℝ N),
    IsZeroMass e →
      fillingInfinityNorm (canonicalFilling e) = prefixInfinityNorm e

end

end MathlibPlus.Open.Algebra.Claim17426
