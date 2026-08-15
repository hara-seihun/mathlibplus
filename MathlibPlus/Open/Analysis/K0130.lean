import Mathlib

namespace MathlibPlus.Open.Analysis

open MeasureTheory

/-- Finite discrete OPE configuration measure: the configuration weight,
partition function, and rank-conditioned probability are given by the
admitted formulas. -/
def finiteDiscreteOPEConfigurationMeasure_8979 : Prop :=
  ∀ (d : ℕ) (x ω : Fin d → ℝ),
    (∀ j, 0 < ω j) →
    (∀ ⦃j k : Fin d⦄, j ≠ k → x j ≠ x k) →
    ∃ W : Finset (Fin d) → ℝ,
      ∃ Z : ℕ → ℝ,
        ∃ P : ℕ → Finset (Fin d) → ℝ,
          (∀ S,
            W S =
              (∏ j ∈ S, ω j) *
                (∏ j ∈ S,
                  ∏ k ∈ S.filter (fun k => j < k),
                    (x j - x k) ^ 2)) ∧
          (∀ r,
            Z r =
              ∑ S : Finset (Fin d),
                if S.card = r then W S else 0) ∧
          (∀ r S, P r S = W S / Z r)

/-- The monic orthogonal-polynomial norm is the adjacent partition-function
ratio in the finite discrete OPE setup. -/
def monicNormAdjacentPartitionRatio_8981 : Prop :=
  ∀ (d : ℕ) (x ω : Fin d → ℝ) (p : ℕ → Polynomial ℝ),
    (∀ j, 0 < ω j) →
    (∀ ⦃j k : Fin d⦄, j ≠ k → x j ≠ x k) →
    let μ : Measure ℝ :=
      ∑ j : Fin d, (ENNReal.ofReal (ω j)) • Measure.dirac (x j)
    let W : Finset (Fin d) → ℝ := fun S =>
      (∏ j ∈ S, ω j) *
        (∏ j ∈ S,
          ∏ k ∈ S.filter (fun k => j < k),
            (x j - x k) ^ 2)
    let Z : ℕ → ℝ := fun r =>
      ∑ S : Finset (Fin d),
        if S.card = r then W S else 0
    let h : ℕ → ℝ := fun n =>
      ∫ z, ((p n).eval z) ^ 2 ∂μ
    (∀ n, n < d → (p n).Monic ∧ (p n).natDegree = n) →
    (∀ m n, m < d → n < d → m ≠ n →
      (∫ z, (p m).eval z * (p n).eval z ∂μ) = 0) →
    ∀ n, n < d → h n = Z (n + 1) / Z n

/-- The exact signed Hellinger identity at a support point for the finite
OPE measure. -/
def exactSignedHellingerSupportPointIdentity_8982 : Prop :=
  ∀ (d : ℕ) (x ω : Fin d → ℝ) (p : ℕ → Polynomial ℝ)
      (i : Fin d) (n : ℕ),
    (∀ j, 0 < ω j) →
    (∀ ⦃j k : Fin d⦄, j ≠ k → x j ≠ x k) →
    let μ : Measure ℝ :=
      ∑ j : Fin d, (ENNReal.ofReal (ω j)) • Measure.dirac (x j)
    let W : Finset (Fin d) → ℝ := fun S =>
      (∏ j ∈ S, ω j) *
        (∏ j ∈ S,
          ∏ k ∈ S.filter (fun k => j < k),
            (x j - x k) ^ 2)
    let Z : ℕ → ℝ := fun r =>
      ∑ S : Finset (Fin d),
        if S.card = r then W S else 0
    let P : ℕ → Finset (Fin d) → ℝ := fun r S => W S / Z r
    let h : ℕ → ℝ := fun k =>
      ∫ z, ((p k).eval z) ^ 2 ∂μ
    (∀ k, k < d → (p k).Monic ∧ (p k).natDegree = k) →
    (∀ m k, m < d → k < d → m ≠ k →
      (∫ z, (p m).eval z * (p k).eval z ∂μ) = 0) →
    n + 1 ≤ d →
    let σ : Finset (Fin d) → ℝ := fun S =>
      Real.sign (∏ j ∈ S, (x i - x j))
    let δ : ℝ :=
      (ω i * ((p n).eval (x i)) ^ 2) / h n
    δ =
      (∑ S ∈
          (Finset.univ.filter
            (fun S : Finset (Fin d) => S.card = n ∧ i ∉ S)),
        σ S *
          Real.sqrt (P n S * P (n + 1) (insert i S))) ^ 2

/-- The OPE occupancy is the rank-r projection-kernel diagonal formula. -/
def opeOccupancyProjectionKernelFormula_8983 : Prop :=
  ∀ (d : ℕ) (x ω : Fin d → ℝ) (p : ℕ → Polynomial ℝ)
      (i : Fin d) (r : ℕ),
    (∀ j, 0 < ω j) →
    (∀ ⦃j k : Fin d⦄, j ≠ k → x j ≠ x k) →
    let μ : Measure ℝ :=
      ∑ j : Fin d, (ENNReal.ofReal (ω j)) • Measure.dirac (x j)
    let W : Finset (Fin d) → ℝ := fun S =>
      (∏ j ∈ S, ω j) *
        (∏ j ∈ S,
          ∏ k ∈ S.filter (fun k => j < k),
            (x j - x k) ^ 2)
    let Z : ℕ → ℝ := fun q =>
      ∑ S : Finset (Fin d),
        if S.card = q then W S else 0
    let P : ℕ → Finset (Fin d) → ℝ := fun q S => W S / Z q
    let h : ℕ → ℝ := fun k =>
      ∫ z, ((p k).eval z) ^ 2 ∂μ
    (∀ k, k < d → (p k).Monic ∧ (p k).natDegree = k) →
    (∀ m k, m < d → k < d → m ≠ k →
      (∫ z, (p m).eval z * (p k).eval z ∂μ) = 0) →
    r ≤ d →
    let κ : ℝ :=
      ∑ S ∈
        (Finset.univ.filter
          (fun S : Finset (Fin d) => S.card = r ∧ i ∈ S)),
        P r S
    κ =
      ω i *
        (∑ k ∈ Finset.range r,
          ((p k).eval (x i)) ^ 2 / h k)

end MathlibPlus.Open.Analysis
