import Mathlib
import MathlibPlus.Analysis.LogarithmicBounds

namespace MathlibPlus.Open.Analysis

/--
For a prime `q`, the local logarithmic increment, normalized by its positive
threshold `T(q)`, is the interval integral of the positive local kernel.
The statement has no hypothesis about global monotonicity of the sequence
`u_k`.
-/
def positive_kernel_integral_factorization_claim9201 : Prop :=
  ∀ (q : ℕ), Nat.Prime q →
    ∀ (T : ℝ),
      1 < T →
      Real.log (q : ℝ) =
        T * (Real.exp (Real.log T / ((q : ℝ) - 1)) - 1) →
      ∀ (y : ℝ),
        1 < y →
        let L : ℝ := Real.log (q : ℝ)
        let Δ_q_y : ℝ :=
          -Real.log (1 - 1 / (q : ℝ)) -
            Real.log (Real.log (y + L) / Real.log y)
        Δ_q_y =
            ∫ v in T..y,
              (1 / (v * Real.log v) -
                1 / ((v + L) * Real.log (v + L))) ∧
          ∀ (v : ℝ),
            1 < v →
            0 <
              1 / (v * Real.log v) -
                1 / ((v + L) * Real.log (v + L))

end MathlibPlus.Open.Analysis
