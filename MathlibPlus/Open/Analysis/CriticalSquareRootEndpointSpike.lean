import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The critical square-root endpoint spike construction: the fixed-interior
profile and first moment do not determine the collision asymptotic.
-/
def critical_square_root_endpoint_spike : Prop :=
  ∀ (τ : ℝ),
    0 ≤ τ →
      ∀ (b : ℕ → ℝ),
        (∀ n : ℕ, 2 ≤ n → 0 < b n) →
          let mass : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun c n j =>
            if j ≤ n - 2 then
              c n * (n : ℝ) ^ 2 /
                (((n + j : ℕ) : ℝ) * ((n + j + 1 : ℕ) : ℝ))
            else if j = n - 1 then
              τ * Real.sqrt (n : ℝ) * c n
            else
              0
          let m : ℕ → ℕ → ℝ := mass b
          let a : ℕ → ℝ := fun n => ∑' j : ℕ, m n j
          let pi_mass : ℕ → ℕ → ℝ := fun n j => m n j / a n
          (∀ s : ℝ,
              0 ≤ s →
                s < 1 →
                  Filter.Tendsto
                    (fun n : ℕ =>
                      m n (Nat.floor (s * (n : ℝ))) / b n)
                    Filter.atTop
                    (nhds (1 / (1 + s) ^ 2))) ∧
            Filter.Tendsto
              (fun n : ℕ => a n / ((n : ℝ) * b n))
              Filter.atTop
              (nhds (1 / 2)) ∧
            Filter.Tendsto
              (fun n : ℕ =>
                (n : ℝ) * ∑' j : ℕ, (pi_mass n j) ^ 2)
              Filter.atTop
              (nhds (7 / 6 + 4 * τ ^ 2)) ∧
            Asymptotics.IsEquivalent Filter.atTop
              (fun n : ℕ => a n)
              (fun n : ℕ => (n : ℝ) * b n / 2) ∧
            Asymptotics.IsEquivalent Filter.atTop
              (fun n : ℕ => ∑' j : ℕ, (pi_mass n j) ^ 2)
              (fun n : ℕ => (7 / 6 + 4 * τ ^ 2) / (n : ℝ)) ∧
            (let W : ℝ → ℝ := fun x =>
              sInf {y : ℝ | 0 ≤ y ∧ y * Real.exp y = x}
             let bW : ℕ → ℝ := fun n =>
              (W (2 * (n : ℝ) / Real.pi)) ^ 2 /
                (16 * (n : ℝ) ^ 2)
             let mW : ℕ → ℕ → ℝ := mass bW
             let aW : ℕ → ℝ := fun n => ∑' j : ℕ, mW n j
             (∀ s : ℝ,
                 0 ≤ s →
                   s < 1 →
                     Filter.Tendsto
                       (fun n : ℕ =>
                         mW n (Nat.floor (s * (n : ℝ))) / bW n)
                       Filter.atTop
                       (nhds (1 / (1 + s) ^ 2))) ∧
               Asymptotics.IsEquivalent Filter.atTop
                 (fun n : ℕ => aW n)
                 (fun n : ℕ =>
                   (W (2 * (n : ℝ) / Real.pi)) ^ 2 /
                     (32 * (n : ℝ)))) ∧
            (0 < τ → 7 / 6 + 4 * τ ^ 2 ≠ (7 : ℝ) / 6)

end MathlibPlus.Open.Analysis
