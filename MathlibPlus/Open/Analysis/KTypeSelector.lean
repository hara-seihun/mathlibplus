import Mathlib

/-!
# Open obligations for the raised K-type selector

Exact formal statements extracted from admitted claims 301--304 (`C-0019`).
The packet's decimal displays for the two safe-window endpoints contain ellipses
and no error tolerance, so the registry uses the exact radical/arccos constants.
-/

open Filter Set Topology

namespace MathlibPlus.Open.Analysis.KTypeSelector

noncomputable section

/-- Claim 301: the exact safe-window characterization for the quadratic
`73x² - 68x + 4`.  The last equality records that the two complementary bad
intervals have the same length `δ₁ - δ₀`. -/
def safeWindow : Prop :=
  let q : ℝ → ℝ := fun x => 73 * x ^ 2 - 68 * x + 4
  let xPlus : ℝ := (34 + 12 * Real.sqrt 6) / 73
  let xMinus : ℝ := (34 - 12 * Real.sqrt 6) / 73
  let δ₀ : ℝ := Real.arccos (Real.sqrt xPlus)
  let δ₁ : ℝ := Real.arccos (Real.sqrt xMinus)
  (∀ Θ ∈ Icc (0 : ℝ) Real.pi,
      0 ≤ q ((Real.cos Θ) ^ 2) ↔
        Θ ∈ (Icc 0 δ₀ ∪ Icc δ₁ (Real.pi - δ₁)) ∪
          Icc (Real.pi - δ₀) Real.pi) ∧
    (Real.pi - δ₀) - (Real.pi - δ₁) = δ₁ - δ₀

/-- Claim 302: the exact phase-increment formula, its positivity, its two
pointwise limits, and divergence of the sum of its increments. -/
def phaseIncrementAsymptotics : Prop :=
  ∀ k : ℝ, 0 < k →
    let A : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 1 / 2
    let B : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 3 / 2
    let ψ : ℕ → ℝ → ℝ := fun m t =>
      ∑ r ∈ Finset.range m,
        (Real.arctan (t / A r) + Real.arctan (t / B r))
    let Θ : ℕ → ℝ → ℝ := fun m t => t * Real.log 2 + ψ m t
    let Δ : ℕ → ℝ → ℝ := fun m t => Θ (m + 1) t - Θ m t
    ∀ t : ℝ, 0 < t →
      (∀ m : ℕ,
          Δ m t = Real.arctan (t / A m) + Real.arctan (t / B m) ∧
            0 < Δ m t) ∧
        Tendsto (fun m : ℕ => Δ m t) atTop (𝓝 0) ∧
        Tendsto (fun m : ℕ => (m : ℝ) * Δ m t) atTop (𝓝 t) ∧
        Tendsto (fun n : ℕ => ∑ m ∈ Finset.range n, Δ m t) atTop atTop

/-- Claim 303: at every real height the safe-selector set has a least natural
index, and its least index at height zero is zero. -/
def finiteSelector : Prop :=
  ∀ k : ℝ, 0 < k →
    let A : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 1 / 2
    let B : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 3 / 2
    let ψ : ℕ → ℝ → ℝ := fun m t =>
      ∑ r ∈ Finset.range m,
        (Real.arctan (t / A r) + Real.arctan (t / B r))
    let Θ : ℕ → ℝ → ℝ := fun m t => t * Real.log 2 + ψ m t
    let q : ℝ → ℝ := fun x => 73 * x ^ 2 - 68 * x + 4
    let Safe : ℝ → ℕ → Prop := fun t m => 0 ≤ q ((Real.cos (Θ m t)) ^ 2)
    (∀ t : ℝ, ∃ m : ℕ, Safe t m ∧ ∀ n : ℕ, Safe t n → m ≤ n) ∧
      Safe 0 0 ∧ ∀ n : ℕ, Safe 0 n → 0 ≤ n

/-- Claim 304: along the phase-locked heights, every fixed K-type tends to the
bad value `1/2`, the convergence is uniform on each bounded finite family, and
no bounded family is safe at every height. -/
def noBoundedSelectorFamily : Prop :=
  ∀ k : ℝ, 0 < k →
    let A : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 1 / 2
    let B : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 3 / 2
    let ψ : ℕ → ℝ → ℝ := fun m t =>
      ∑ r ∈ Finset.range m,
        (Real.arctan (t / A r) + Real.arctan (t / B r))
    let Θ : ℕ → ℝ → ℝ := fun m t => t * Real.log 2 + ψ m t
    let q : ℝ → ℝ := fun x => 73 * x ^ 2 - 68 * x + 4
    let tSeq : ℕ → ℝ := fun n => ((n : ℝ) * Real.pi + Real.pi / 4) / Real.log 2
    q (1 / 2) < 0 ∧
      (∀ m : ℕ,
        Tendsto (fun n : ℕ => (Real.cos (Θ m (tSeq n))) ^ 2)
          atTop (𝓝 (1 / 2))) ∧
      (∀ M : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ, m ≤ M →
          |(Real.cos (Θ m (tSeq n))) ^ 2 - 1 / 2| < ε) ∧
      ∀ M : ℕ, ∃ n : ℕ, ∀ m : ℕ, m ≤ M →
        q ((Real.cos (Θ m (tSeq n))) ^ 2) < 0

end

end MathlibPlus.Open.Analysis.KTypeSelector
