import Mathlib

open scoped BigOperators Interval

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity registry node for the moderate-tail part of the C-0044
prime-counting certificate.  The logarithmic integral and the normalized
prime-counting error are expanded at their displayed carriers.
-/

/-- On `40 ≤ L ≤ 44`, the signed normalized PNT error has the displayed
square-root bound and the displayed pointwise margin below `B₋`. -/
noncomputable def moderateTailPNTErrorBound : Prop :=
  let Li : ℝ → ℝ := fun x => ∫ t in (2 : ℝ)..x, 1 / Real.log t
  let Epi : ℝ → ℝ := fun x =>
    ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) / (x / Real.log x)
  let eta : ℝ := 0.024334
  let c : ℝ := 1673823191040000 / 23
  let Bminus : ℝ → ℝ := fun L =>
    eta / L ^ 3 + eta / L ^ 4 + 5 * eta / L ^ 5 + 1057.2 / L ^ 7 -
      (∑ j ∈ Finset.Icc 8 15, (Nat.factorial j : ℝ) / L ^ j) -
      c / L ^ 16
  ∀ L : ℝ, 40 ≤ L → L ≤ 44 →
    Epi (Real.exp L) ≤ L ^ 2 * Real.exp (-L / 2) / (8 * Real.pi) ∧
      (1.6135 : ℝ) / 10 ^ (7 : ℕ) <
        Bminus L - L ^ 2 * Real.exp (-L / 2) / (8 * Real.pi)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
