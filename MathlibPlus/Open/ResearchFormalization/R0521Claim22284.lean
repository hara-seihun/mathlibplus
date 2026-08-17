import Mathlib

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization.R0521Claim22284

noncomputable section

/-- The explicit dense-tail gap train from Claim 22284. -/
def denseTailGap (q ε : ℝ) (i : ℤ) : ℝ :=
  (ε + q ^ i.natAbs) / (1 + ε)

/-- The recursively based roots, normalized by `x₀ = 0`. -/
def denseTailRoot (q ε : ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i then
    ∑ n ∈ Finset.range i.natAbs, denseTailGap q ε (n : ℤ)
  else
    -∑ n ∈ Finset.range i.natAbs,
      denseTailGap q ε (-((n : ℤ) + 1))

/-- No bounded interval contains infinitely many members of a root train. -/
def noFiniteAccumulation (x : ℤ → ℝ) : Prop :=
  ∀ (a b : ℝ), {i : ℤ | a ≤ x i ∧ x i ≤ b}.Finite

/-- Claim 22284: the positive dense-tail gap train, its recursive roots, the
    positive limiting spacing, and the two-sided escape/no-accumulation facts. -/
def denseTailCounterexampleGapTrain_claim22284 : Prop :=
  ∀ (q ε : ℝ), 0 < q → q < 1 → 0 < ε →
    let d := denseTailGap q ε
    let x := denseTailRoot q ε
    d 0 = 1 ∧
      (∀ i : ℤ, 0 < d i) ∧
      StrictMono x ∧
      (∀ i : ℤ, x (i + 1) - x i = d i) ∧
      0 < ε / (1 + ε) ∧
      Filter.Tendsto (fun n : ℕ => d (Int.ofNat n)) atTop
        (𝓝 (ε / (1 + ε))) ∧
      Filter.Tendsto (fun n : ℕ => d (-(Int.ofNat n))) atTop
        (𝓝 (ε / (1 + ε))) ∧
      Filter.Tendsto (fun n : ℕ => x (Int.ofNat n)) atTop atTop ∧
      Filter.Tendsto (fun n : ℕ => x (-(Int.ofNat n))) atTop atBot ∧
      noFiniteAccumulation x

end

end MathlibPlus.Open.ResearchFormalization.R0521Claim22284
