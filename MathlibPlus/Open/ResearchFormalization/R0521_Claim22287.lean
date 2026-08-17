import MathlibPlus.Open.Analysis.ResearchFormalizeR0438

open Filter
open scoped BigOperators Topology

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0521.Claim22287

open MathlibPlus.Open.Analysis

/-- The normalized dense-tail gap train. -/
def denseTailGap (q ε : ℝ) (i : ℤ) : ℝ :=
  (ε + q ^ Int.natAbs i) / (1 + ε)

/-- Roots obtained recursively from the dense-tail gaps, with x₀ = 0. -/
def denseTailRoot (q ε : ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i then
    ∑ k ∈ Finset.range (Int.toNat i), denseTailGap q ε (k : ℤ)
  else
    -∑ k ∈ Finset.range (Int.toNat (-i)),
      denseTailGap q ε (-((k : ℤ) + 1))

/-- No bounded interval contains infinitely many indexed roots. -/
def noFiniteAccumulation (x : ℤ → ℝ) : Prop :=
  ∀ a b : ℝ, Set.Finite {i : ℤ | a ≤ x i ∧ x i ≤ b}

/-- The exact O(j⁻²) tail assertion for one adjacent pressure series. -/
def pressureSummandHasQuadraticTail (x : ℤ → ℝ) (i : ℤ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ m : {m : ℤ // m ≠ i ∧ m ≠ i + 1},
      N ≤ Int.natAbs (m.1 - i) →
        ‖pressureTerm x i m.1‖ ≤
          C / (Int.natAbs (m.1 - i) : ℝ) ^ 2

/-- Claim 22287: the explicit dense-tail roots have quadratic pressure tails and
absolute convergence at every adjacent pair. -/
def claim22287 : Prop :=
  ∀ (q ε : ℝ), 0 < q → q < 1 → 0 < ε →
    let x := denseTailRoot q ε
    gap x 0 = 1 ∧
      (∀ i : ℤ, gap x i = denseTailGap q ε i) ∧
      (∀ i : ℤ, 0 < gap x i) ∧
      StrictMono x ∧
      Tendsto (fun i : ℤ => gap x i) atTop
        (𝓝 (ε / (1 + ε))) ∧
      Tendsto (fun i : ℤ => gap x i) atBot
        (𝓝 (ε / (1 + ε))) ∧
      Tendsto x atTop atTop ∧
      Tendsto x atBot atBot ∧
      noFiniteAccumulation x ∧
      ∀ i : ℤ,
        pressureSummandHasQuadraticTail x i ∧
          AbsolutelyConvergentPressure x i

end MathlibPlus.Open.ResearchFormalization.R0521.Claim22287
