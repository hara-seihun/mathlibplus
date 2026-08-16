import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The finite configurations of rank `r` on a support of size `d`. -/
def opeConfigurations (d r : ℕ) : Finset (Finset (Fin d)) :=
  (Finset.univ : Finset (Fin d)).powerset.filter (fun S => S.card = r)

/-- The finite discrete OPE configuration weight. -/
def opeWeight {d : ℕ} (x ω : Fin d → ℝ) (S : Finset (Fin d)) : ℝ :=
  (∏ j ∈ S, ω j) *
    (∏ j ∈ S, (∏ k ∈ S.filter (fun k => j < k), (x j - x k) ^ 2))

/-- The rank partition function of the finite discrete OPE. -/
def opePartitionFunction {d : ℕ} (x ω : Fin d → ℝ) (r : ℕ) : ℝ :=
  ∑ S ∈ opeConfigurations d r, opeWeight x ω S

/-- The finite discrete OPE configuration probability. -/
def opeProbability {d : ℕ} (x ω : Fin d → ℝ) (r : ℕ)
    (S : Finset (Fin d)) : ℝ :=
  opeWeight x ω S / opePartitionFunction x ω r

/-- Occupancy as the OPE mass of configurations containing the support site. -/
def opeKappa {d : ℕ} (x ω : Fin d → ℝ) (r : ℕ) (i : Fin d) : ℝ :=
  ∑ S ∈ opeConfigurations d r, if i ∈ S then opeProbability x ω r S else 0

/-- The rank-ordered orthogonal-polynomial data used by the OPE projection kernel. -/
def opePolynomialSequence {d : ℕ} (x ω : Fin d → ℝ)
    (p : ℕ → Polynomial ℝ) (h : ℕ → ℝ) : Prop :=
  (∀ k, k < d → p k ≠ 0 ∧ (p k).natDegree = k) ∧
    (∀ k l, k < d → l < d → k ≠ l →
      (∑ i : Fin d, ω i * (p k).eval (x i) * (p l).eval (x i)) = 0) ∧
    (∀ k, k < d →
      h k = ∑ i : Fin d, ω i * ((p k).eval (x i)) ^ 2 ∧ 0 < h k)

/-- The rank-`n` residual appearing in the OPE projection kernel. -/
def opeResidual {d : ℕ} (x ω : Fin d → ℝ)
    (p : ℕ → Polynomial ℝ) (h : ℕ → ℝ) (n : ℕ) (i : Fin d) : ℝ :=
  ω i * ((p n).eval (x i)) ^ 2 / h n

/-- Residual equals the rank-one occupancy increment. -/
def residualEqualsRankOneOccupancyIncrement_8984 : Prop :=
  ∀ (d n : ℕ) (x ω : Fin d → ℝ)
    (p : ℕ → Polynomial ℝ) (h : ℕ → ℝ),
    n + 1 ≤ d →
    Function.Injective x →
    (∀ i, 0 < ω i) →
    opePolynomialSequence x ω p h →
    ∀ i : Fin d,
      opeResidual x ω p h n i =
        opeKappa x ω (n + 1) i - opeKappa x ω n i

/-- The vacant sector normalized on rank-`n` configurations avoiding `i`. -/
def qMinus {d : ℕ} (x ω : Fin d → ℝ) (n : ℕ) (i : Fin d)
    (S : Finset (Fin d)) : ℝ :=
  opeProbability x ω n S /
    (∑ T ∈ opeConfigurations d n,
      if i ∉ T then opeProbability x ω n T else 0)

/-- The occupied sector normalized on rank-`n+1` configurations containing `i`. -/
def qPlus {d : ℕ} (x ω : Fin d → ℝ) (n : ℕ) (i : Fin d)
    (S : Finset (Fin d)) : ℝ :=
  opeProbability x ω (n + 1) (insert i S) /
    (∑ T ∈ opeConfigurations d n,
      if i ∉ T then opeProbability x ω (n + 1) (insert i T) else 0)

/-- Normalized vacant and occupied sectors on the common configuration space. -/
def normalizedVacantAndOccupiedSectors_8985 : Prop :=
  ∀ (d n : ℕ) (x ω : Fin d → ℝ),
    n + 1 ≤ d →
    Function.Injective x →
    (∀ i, 0 < ω i) →
    ∀ (i : Fin d) (S : Finset (Fin d)),
      S.card = n →
      i ∉ S →
      qMinus x ω n i S =
          opeProbability x ω n S / (1 - opeKappa x ω n i) ∧
        qPlus x ω n i S =
          opeProbability x ω (n + 1) (insert i S) /
            opeKappa x ω (n + 1) i

end MathlibPlus.Open.Analysis
