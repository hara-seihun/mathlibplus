import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 692: the C-0044 factorial-720 majorant bounds real prime counting
on the complete domain `x > 1`, with the real cutoff interpreted by `Nat.floor`.
-/
def globalFactorial720PrimeCountingBound : Prop :=
  let F : ℝ → ℝ := fun x =>
    let L := Real.log x
    x / L + x / L ^ 2 + 2 * x / L ^ 3 +
      6.024334 * x / L ^ 4 +
      24.024334 * x / L ^ 5 +
      120.12167 * x / L ^ 6 +
      720 * x / L ^ 7 +
      6097.2 * x / L ^ 8
  ∀ x : ℝ, 1 < x →
    (Nat.primeCounting (Nat.floor x) : ℝ) < F x

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
