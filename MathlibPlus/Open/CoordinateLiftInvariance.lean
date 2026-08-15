import Mathlib

namespace MathlibPlus.Open

open Filter Asymptotics
open scoped Topology

/--
If the scale has subexponential logarithmic growth and the matched physical and
lifted coordinates converge to a positive lifted coordinate, the exponential
rate of the displacement is unchanged by the lift
`x = s ^ 2 * z ^ 2`.
-/
def coordinateLiftInvariance
    (s zₙ yₙ : ℕ → ℝ) (z rate : ℝ) : Prop :=
  IsLittleO atTop (fun n => Real.log (s n)) (fun n => (n : ℝ)) ∧
    Tendsto zₙ atTop (𝓝 z) ∧
    Tendsto yₙ atTop (𝓝 z) ∧
    0 < z ∧
    (Tendsto
        (fun n : ℕ =>
          -(1 / (n : ℝ)) *
            Real.log |s n ^ 2 * zₙ n ^ 2 - s n ^ 2 * yₙ n ^ 2|)
        atTop (𝓝 rate) ↔
      Tendsto
        (fun n : ℕ => -(1 / (n : ℝ)) * Real.log |zₙ n - yₙ n|)
        atTop (𝓝 rate))

end MathlibPlus.Open
