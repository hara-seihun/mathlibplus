import MathlibPlus.Analysis.Claim11285
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace MathlibPlus.Open.Analysis

/--
The unresolved complete-monotonicity component of claim 11285.  The source
uses a complex rational expression; this registry node makes its real-axis
interpretation explicit by taking the real part and quantifying on `x > 0`.
-/
def completelyMonotoneLogDerivative_claim11285 : Prop :=
  ∀ (n : ℕ) (x : ℝ), 0 < x →
    0 ≤ (-1 : ℝ) ^ n *
      iteratedDeriv n
        (fun y : ℝ =>
          (MathlibPlus.Analysis.Claim11285.descendedLogDerivative
            (y : ℂ)).re) x

end MathlibPlus.Open.Analysis
