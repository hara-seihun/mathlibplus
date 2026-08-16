import Mathlib

namespace MathlibPlus.Open.Analysis

open Filter

/-- The exact bivariate generating-function carrier for the derivative kernel. -/
def derivativeKernelCarrier (S : ℕ → ℕ → ℝ → ℝ) : Prop :=
  let a : ℝ → ℝ := fun u =>
    u / (1 - u / 2) + u / (2 * (1 + u / 2)) +
        (1 / 2) * Real.log (1 + u / 2) -
        u ^ 2 / (6 * (1 + u / 2) ^ 2) +
        u ^ 4 / (15 * (1 + u / 2) ^ 4)
  let Z : ℝ → ℝ := fun s => (1 + s) / (1 - s)
  let W : ℝ → ℝ := fun t => (1 + t) / (1 - t)
  ∀ u s t : ℝ,
    0 < u → u < 2 →
    abs s < (1 / 4 : ℝ) → abs t < (1 / 4 : ℝ) → s ≠ t →
      (∑' i : ℕ, ∑' j : ℕ, S i j u * s ^ i * t ^ j) =
        ((Z s + 1) * (W t + 1) / (2 * (Z s ^ 2 - W t ^ 2))) *
          (Z s ^ 2 * deriv a (u * Z s) - W t ^ 2 * deriv a (u * W t))

/-- No finite radius supports row-diagonal dominance uniformly in the order. -/
def noOrderUniformRowDominanceRay : Prop :=
  ∃ S : ℕ → ℕ → ℝ → ℝ,
    derivativeKernelCarrier S ∧
      ∀ r : ℝ, r > (1 / 2 : ℝ) →
        let a : ℝ → ℝ := fun u =>
          u / (1 - u / 2) + u / (2 * (1 + u / 2)) +
              (1 / 2) * Real.log (1 + u / 2) -
              u ^ 2 / (6 * (1 + u / 2) ^ 2) +
              u ^ 4 / (15 * (1 + u / 2) ^ 4)
        let W : ℝ → ℝ := fun t => (1 + t) / (1 - t)
        let q : ℝ := (2 * r - 1) / (2 * r + 1)
        let A : ℝ := 64 * r ^ 4 / ((2 * r - 1) * (2 * r + 1) ^ 4)
        let F : ℝ → ℝ := fun t =>
          if t = 0 then S 0 0 (1 / r)
          else
            ((W t + 1) / (1 - W t ^ 2)) *
              (deriv a (1 / r) - W t ^ 2 * deriv a ((1 / r) * W t))
        let p : ℝ → ℕ → ℕ → ℝ := fun ρ i j =>
          (if i = j then 1 / (2 * ρ) else 0) -
            (1 / ρ ^ 2) * S i j (1 / ρ)
        let P : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ :=
          fun n ρ i j => p ρ (i : ℕ) (j : ℕ)
        let rowSum : ℝ → ℕ → ℕ → ℝ := fun ρ n i =>
          ∑ j ∈ Finset.range n, p ρ i j
        let rowDominant : ℕ → ℝ → Prop := fun n ρ =>
          0 < n ∧
            (∀ i j : Fin n, i ≠ j → P n ρ i j ≤ 0) ∧
            (∀ i : Fin n, 0 ≤ ∑ j : Fin n, P n ρ i j)
        0 < q ∧ q < 1 ∧
          (∀ t : ℝ, 0 < t → t < q → AnalyticAt ℝ F t) ∧
          (∃ ε : ℝ, 0 < ε ∧
            ∀ t : ℝ, 0 < abs (t - q) → abs (t - q) < ε →
              AnalyticAt ℝ F t) ∧
          ¬ AnalyticAt ℝ F q ∧
          Tendsto (fun t : ℝ => (t - q) ^ 2 * F t) (nhdsWithin q ({q}ᶜ)) (nhds A) ∧
          0 < A ∧
          (∀ t : ℝ, abs t < q →
            F t = ∑' j : ℕ, S 0 j (1 / r) * t ^ j) ∧
          (∀ᶠ j in (atTop : Filter ℕ), 0 < S 0 j (1 / r)) ∧
          Tendsto
            (fun j : ℕ =>
              S 0 j (1 / r) /
                (((j + 1 : ℕ) : ℝ) * (q ^ (j + 2))⁻¹))
            atTop (nhds A) ∧
          (∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → rowSum r n 0 < 0) ∧
          ¬ (∃ R : ℝ, R > (1 / 2 : ℝ) ∧
            ∀ ρ : ℝ, R ≤ ρ →
              ∀ n : ℕ, 0 < n → rowDominant n ρ)

/-- The exact order-eleven determinant and row-sum failure at radius 75. -/
def exactOrderElevenFailureAtRadius75 : Prop :=
  ∃ S : ℕ → ℕ → ℝ → ℝ,
    derivativeKernelCarrier S ∧
      let p : ℝ → ℕ → ℕ → ℝ := fun r i j =>
        (if i = j then 1 / (2 * r) else 0) -
          (1 / r ^ 2) * S i j (1 / r)
      let P : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ :=
        fun n r i j => p r (i : ℕ) (j : ℕ)
      let rowSum : ℝ → ℕ → ℕ → ℝ := fun r n i =>
        ∑ j ∈ Finset.range n, p r i j
      rowSum 75 11 0 =
          -((388390698048613639296611139428382586107113872969216098723050 : ℝ) /
            (1303324760524543315061971545631739633725909680957223948197224549 : ℝ)) ∧
        (∀ k : ℕ, 0 < k → k ≤ 10 → 0 < Matrix.det (P k 75)) ∧
        Matrix.det (P 11 75) < 0 ∧
        (∑ i : Fin 11, ∑ j : Fin 11, P 11 75 i j) < 0

/-- The locally uniform coefficient and linear-order row-sum scaling laws. -/
def linearOrderCoefficientScalingLaw : Prop :=
  ∃ S : ℕ → ℕ → ℝ → ℝ,
    derivativeKernelCarrier S ∧
      let phi : ℝ → ℝ := fun z =>
        2 * (z + 1) * Real.exp z +
          ((-8 / 45) * z ^ 4 + (32 / 45) * z ^ 3 +
              (2 / 3) * z ^ 2 - (7 / 3) * z + 3 / 2) * Real.exp (-z)
      let I : ℝ → ℝ := fun α =>
        Real.exp (-α) / 90 *
          (16 * α ^ 4 - 60 * α ^ 2 + 180 * α * Real.exp (2 * α) +
            90 * α + 45 * Real.exp α - 45)
      let p : ℝ → ℕ → ℕ → ℝ := fun r i j =>
        (if i = j then 1 / (2 * r) else 0) -
          (1 / r ^ 2) * S i j (1 / r)
      (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ici 0 →
        ∀ ε : ℝ, 0 < ε →
          ∃ R : ℝ, R > (1 / 2 : ℝ) ∧
            ∀ r : ℝ, R < r →
              ∀ j : ℕ, (j : ℝ) / r ∈ K →
                abs (S 0 j (1 / r) - phi ((j : ℝ) / r)) < ε) ∧
      (∀ α : ℝ, 0 ≤ α →
        ∀ rseq : ℕ → ℝ, ∀ nseq : ℕ → ℕ,
          Tendsto rseq atTop atTop →
          Tendsto (fun k : ℕ => (nseq k : ℝ) / rseq k)
            atTop (nhds α) →
          Tendsto
              (fun k : ℕ =>
                (1 / rseq k) *
                  ∑ j ∈ Finset.range (nseq k), S 0 j (1 / rseq k))
              atTop (nhds (I α)) ∧
          Tendsto
              (fun k : ℕ =>
                rseq k *
                  ∑ j ∈ Finset.range (nseq k), p (rseq k) 0 j)
              atTop (nhds (1 / 2 - I α)))

/-- The unique positive row-sum transition constant and its exact bounds. -/
def uniqueRowSumTransitionConstant : Prop :=
  let phi : ℝ → ℝ := fun z =>
    2 * (z + 1) * Real.exp z +
      ((-8 / 45) * z ^ 4 + (32 / 45) * z ^ 3 +
          (2 / 3) * z ^ 2 - (7 / 3) * z + 3 / 2) * Real.exp (-z)
  let I : ℝ → ℝ := fun α =>
    Real.exp (-α) / 90 *
      (16 * α ^ 4 - 60 * α ^ 2 + 180 * α * Real.exp (2 * α) +
        90 * α + 45 * Real.exp α - 45)
  (∀ z : ℝ, 0 ≤ z → 0 < phi z) ∧
    (∀ x y : ℝ, 0 ≤ x → x < y → I x < I y) ∧
    I 0 = 0 ∧
    Tendsto I atTop atTop ∧
    (∀ α : ℝ,
      I α = 1 / 2 ↔
        16 * α ^ 4 - 60 * α ^ 2 + 90 * α - 45 +
            180 * α * Real.exp (2 * α) = 0) ∧
    (∃ αstar : ℝ,
      0 ≤ αstar ∧
        I αstar = 1 / 2 ∧
        (∀ β : ℝ, 0 ≤ β → I β = 1 / 2 → β = αstar) ∧
        0.14059966383383500 < αstar ∧
        αstar < 0.14059966383383501 ∧
        7.1123925387320316 < αstar⁻¹ ∧
        αstar⁻¹ < 7.1123925387320323)

end MathlibPlus.Open.Analysis
