import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0325

noncomputable section

open scoped BigOperators

/-- The five source labels in the O-0325 boundary split. -/
abbrev SourceChannel := Fin 5

def shadow : SourceChannel := 0
def cutoff : SourceChannel := 1
def sourceCorrectionRestoration : SourceChannel := 2
def dini : SourceChannel := 3
def completeAlias : SourceChannel := 4

def nonshadowChannels : Finset SourceChannel :=
  (Finset.univ : Finset SourceChannel).erase shadow

/-- The normalized two-row first-jet matrix, with one column per labelled
source channel. -/
noncomputable def firstJetMatrix (L : ℕ)
    (V : SourceChannel → ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) SourceChannel ℂ :=
  fun row ν =>
    if row = 0 then V ν z else (L : ℂ)⁻¹ * deriv (V ν) z

/-- The unnormalized source-labelled pairwise minor. -/
noncomputable def pairwiseMinor (V : SourceChannel → ℂ → ℂ)
    (μ ν : SourceChannel) (z : ℂ) : ℂ :=
  V μ z * deriv (V ν) z - deriv (V μ) z * V ν z

/-- The determinant of the two columns indexed by μ and ν in the normalized
first-jet matrix. -/
noncomputable def pairwiseJetDeterminant (L : ℕ)
    (V : SourceChannel → ℂ → ℂ)
    (μ ν : SourceChannel) (z : ℂ) : ℂ :=
  Matrix.det (fun i j : Fin 2 =>
    firstJetMatrix L V z i (![μ, ν] j))

/-- The aggregate unnormalized determinant of the shadow and nonshadow sums. -/
noncomputable def aggregateMinor (V : SourceChannel → ℂ → ℂ) (z : ℂ) : ℂ :=
  V shadow z *
      deriv (fun w => ∑ ν ∈ nonshadowChannels, V ν w) z -
    deriv (V shadow) z * (∑ ν ∈ nonshadowChannels, V ν z)

/-- The determinant of the normalized two-column matrix whose columns are the
shadow channel and the aggregate nonshadow channel. -/
noncomputable def aggregateJetDeterminant (L : ℕ)
    (V : SourceChannel → ℂ → ℂ) (z : ℂ) : ℂ :=
  Matrix.det (fun i j : Fin 2 =>
    if j = 0 then
      firstJetMatrix L V z i shadow
    else
      ∑ ν ∈ nonshadowChannels, firstJetMatrix L V z i ν)

/-- Claim 15403: the exact five labelled channels retain their normalized
first-jet matrix, all pairwise minors with the normalization factor explicit,
and the aggregate shadow/nonshadow determinant sum. -/
def sourceLabeledFirstJetMatrixClaim15403 : Prop :=
  ∀ (L : ℕ), 0 < L →
    ∀ V : SourceChannel → ℂ → ℂ,
      (∀ ν, Differentiable ℂ (V ν)) →
      (∀ μ ν z,
        pairwiseJetDeterminant L V μ ν z =
          (L : ℂ)⁻¹ * pairwiseMinor V μ ν z) ∧
      (∀ z,
        aggregateJetDeterminant L V z =
          (L : ℂ)⁻¹ * aggregateMinor V z) ∧
      (∀ z,
        aggregateMinor V z =
          ∑ ν ∈ nonshadowChannels, pairwiseMinor V shadow ν z)

end

end MathlibPlus.Open.ResearchFormalization.O0325
