import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathlibPlus.Analysis

/-!
Statement-fidelity formalization of admitted claim 4393.  The arithmetic
logarithm is represented by an arbitrary complex function `p`; indexing by the
subtype `n ≥ 2` makes the common ordinary-integer exponents explicit, and the
second conjunct records absolute convergence in every real half-plane.
-/
def ordinaryDirichletLogarithm (p : ℂ → ℂ) : Prop :=
  ∃ b : {n : ℕ // 2 ≤ n} → ℂ,
    (∀ s : ℂ, 1 < s.re →
      p s = ∑' n, b n * ((n.1 : ℂ) ^ (-s))) ∧
    (∀ σ : ℝ, 1 < σ →
      Summable (fun n => ‖b n‖ * (n.1 : ℝ) ^ (-σ)))

end MathlibPlus.Analysis
