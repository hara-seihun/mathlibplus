import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace MathlibPlus.Analysis

/-!
# Integral-divisor moment sequences (claim 4733)

The source supplies positive nodes, natural multiplicities, a finite first
moment, and the displayed moment representation.  The convergence convention
for higher moments is deliberately not strengthened here: the definition uses
Lean's `tsum` exactly for the displayed sequence equations.
-/

/-- A real sequence represented by positive nodes with integral multiplicities. -/
def integralDivisorMomentSequence (q : ℕ → ℝ) : Prop :=
  ∃ (m : ℕ → ℕ) (t : ℕ → ℝ),
    (∀ j, 0 < t j) ∧
    Summable (fun j => (m j : ℝ) * t j) ∧
    (∀ n, q n = ∑' j, (m j : ℝ) * (t j) ^ n)

end MathlibPlus.Analysis
