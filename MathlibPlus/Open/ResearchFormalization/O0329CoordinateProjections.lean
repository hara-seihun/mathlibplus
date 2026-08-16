import Mathlib

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MathlibPlus.Open.ResearchFormalization.O0329

private abbrev H := lp (fun _ : ℕ => ℝ) (2 : ENNReal)

private def basisVector (j : ℕ) : H :=
  lp.single (2 : ENNReal) j 1

private def projection (j : ℕ) : H →L[ℝ] H :=
  (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ENNReal) j).smulRight (basisVector j)

private def operatorNormPrecompact (S : Set (H →L[ℝ] H)) : Prop :=
  IsCompact (closure S)

/-- Claim 15496: the standard real `ℓ²(ℕ)` coordinate projection is the
rank-one projection `x ↦ ⟪x,e_j⟫ e_j`. -/
def coordinateRankOneProjection : Prop :=
  Orthonormal ℝ basisVector ∧
    ∀ (j : ℕ) (x : H),
      projection j x = inner ℝ x (basisVector j) • basisVector j

/-- Claim 15501: the weakly-null standard basis and the pointwise/weakly-null
coordinate observers still track the moving diagonal exactly. -/
def perfectMovingDiagonalTracking : Prop :=
  (∀ (y : H),
    Tendsto (fun j : ℕ => inner ℝ (basisVector j) y)
      atTop (𝓝 0)) ∧
  (∀ (x : H),
    Tendsto (fun j : ℕ => projection j x)
      atTop (𝓝 0)) ∧
  (∀ (x y : H),
    Tendsto (fun j : ℕ => inner ℝ (projection j x) y)
      atTop (𝓝 0)) ∧
  (∀ (j : ℕ),
    projection j (basisVector j) = basisVector j ∧
      ‖projection j (basisVector j)‖ = 1)

/-- Claim 15502: distinct coordinate projections are one apart in operator
norm, with the coordinate-square upper bound and the diagonal witness. -/
def exactPairwiseOperatorNormDistance : Prop :=
  ∀ (i j : ℕ), i ≠ j →
    ‖projection i - projection j‖ = 1 ∧
    ‖(projection i - projection j) (basisVector i)‖ = 1 ∧
    (∀ (x : H),
      ‖(projection i - projection j) x‖ ^ 2 =
          |x i| ^ 2 + |x j| ^ 2 ∧
        |x i| ^ 2 + |x j| ^ 2 ≤ ‖x‖ ^ 2)

/-- Claim 15503: strong and weak convergence to zero coexist with exact
operator-norm separation, so there is neither a norm-Cauchy subsequence nor
operator-norm precompactness. -/
def strongConvergenceNotOperatorNormPrecompact : Prop :=
  (∀ (x : H),
    Tendsto (fun j : ℕ => projection j x)
      atTop (𝓝 0)) ∧
  (∀ (x y : H),
    Tendsto (fun j : ℕ => inner ℝ (projection j x) y)
      atTop (𝓝 0)) ∧
  (∀ (i j : ℕ), i ≠ j →
    ‖projection i - projection j‖ = 1) ∧
  (¬ ∃ (φ : ℕ → ℕ),
    StrictMono φ ∧
      CauchySeq (fun n : ℕ => projection (φ n))) ∧
  ¬ operatorNormPrecompact (Set.range projection)

end MathlibPlus.Open.ResearchFormalization.O0329
