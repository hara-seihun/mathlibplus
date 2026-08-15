import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact rank-period expansion and positivity claim for the mixed-shell witness. -/
def mixedShellRankPeriodExpansion : Prop :=
  let e : Polynomial ℚ :=
    (1 + Polynomial.C (2 : ℚ) * Polynomial.X) * (1 + Polynomial.X) *
      (1 + Polynomial.X + Polynomial.X ^ 2) *
      (1 + Polynomial.C (9 / 10 : ℚ) * Polynomial.X)
  let eNeg : Polynomial ℚ := e.comp (-Polynomial.X)
  let h : ℕ → ℚ := fun m =>
    PowerSeries.coeff m ((Polynomial.toPowerSeries eNeg)⁻¹)
  let d : ℕ → ℚ := fun r =>
    -Matrix.det (fun i j : Fin 2 => h (r - 1 + i.val + j.val))
  let a : Fin 6 → ℚ :=
    ![(132800 : ℚ) / 3003, 54400 / 1001, 16000 / 273,
      4800 / 91, 128000 / 3003, 38400 / 1001]
  let c : Fin 6 → ℚ :=
    ![(2000 : ℚ) / 273, 300 / 91, -1000 / 273,
      -600 / 91, -100 / 39, 400 / 91]
  let f : Fin 6 → ℚ :=
    ![-(17496 : ℚ) / 5005, -8748 / 5005, 2187 / 910,
      2187 / 455, 2187 / 715, -2187 / 2002]
  (∀ r : ℕ, 1 ≤ r →
    let n := r - 1
    let s : Fin 6 := ⟨n % 6, Nat.mod_lt n (by norm_num)⟩
    Nat.ModEq 6 s.val n ∧
      d r = a s * (2 : ℚ) ^ n - (17496 / 455 : ℚ) * (9 / 5 : ℚ) ^ n +
        c s + f s * (9 / 10 : ℚ) ^ n) ∧
  (∀ s : Fin 6,
    a s ≥ (38400 : ℚ) / 1001 ∧
    |c s| ≤ (2000 : ℚ) / 273 ∧
    |f s| ≤ (2187 : ℚ) / 455) ∧
  (∀ n : ℕ, 2 ≤ n → 0 < d (n + 1)) ∧
  d 1 = (48 : ℚ) / 5 ∧ d 2 = (206 : ℚ) / 5

end MathlibPlus.Open.Analysis
