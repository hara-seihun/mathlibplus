import MathlibPlus.Open.ResearchFormalization.R2294Weights

namespace MathlibPlus.Open.ResearchFormalization.R2294

noncomputable section

open scoped BigOperators

/-- Claim 44254: the displayed absolute support represents `w_16`; its
certificate residual first reaches zero at 46, while the canonical greedy
residual first reaches zero at 392. -/
def claim44254 : Prop :=
  let absoluteSupport : Finset ℕ :=
    {17, 18, 19, 22, 23, 24, 28, 32, 33, 34, 35, 36, 39, 42, 43, 45, 46}
  let certificateResidual : ℕ → ℕ := fun j =>
    Nat.rec 16 (fun i r =>
      2 * r -
        (16 + i + 1) *
          (if 16 + i + 1 ∈ absoluteSupport then 1 else 0)) j
  let greedyResidual : ℕ → ℕ := fun j =>
    Nat.rec 16 (fun i r =>
      if 2 * r ≥ 16 + i + 1 then
        2 * r - (16 + i + 1)
      else
        2 * r) j
  supportWeightSum absoluteSupport = erdosWeight 16 ∧
    certificateResidual 30 = 0 ∧
      (∀ j : ℕ, j < 30 → certificateResidual j ≠ 0) ∧
        greedyResidual 376 = 0 ∧
          (∀ j : ℕ, j < 376 → greedyResidual j ≠ 0)

/-- Claim 44257: a centered zero-to-zero block is equivalent to the
corresponding signed dyadic moment cancellation, and the two feasible next
children occur exactly in the unit branch strip. -/
def claim44257 : Prop :=
  (∀ (N M : ℕ) (ε : ℕ → ℤ),
      N ≤ M →
        (∀ k : ℕ, k ∈ Finset.Icc (N + 1) M →
          ε k = -1 ∨ ε k = 1) →
          let path : ℕ → ℤ := fun j =>
            Nat.rec 0 (fun i v =>
              2 * v +
                ((N + i + 1 : ℕ) : ℤ) * ε (N + i + 1)) j
          path (M - N) = 0 ↔
            (∑ k ∈ Finset.Icc (N + 1) M,
              (ε k : ℚ) * (k : ℚ) / (2 : ℚ) ^ k) = 0) ∧
    (∀ (N : ℕ) (v : ℤ),
      |v| ≤ (N : ℤ) + 2 →
        let step : Bool → ℤ := fun d =>
          2 * v + ((N : ℤ) + 1) *
            (1 - 2 * (if d then 1 else 0))
        ((|step false| ≤ (N : ℤ) + 3) ∧
          (|step true| ≤ (N : ℤ) + 3) ↔ |v| ≤ 1))

end

end MathlibPlus.Open.ResearchFormalization.R2294
