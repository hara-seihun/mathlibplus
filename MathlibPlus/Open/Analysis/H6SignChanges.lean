import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def h6Log (x : ℝ) : ℝ :=
  (1 / 12 : ℝ) * (∑ n ∈ Finset.Icc 1 (Nat.floor x),
    ((n : ℝ) / x) ^ 2 * (1 - ((n : ℝ) / x) ^ 2) ^ 3 *
      (11 * ((n : ℝ) / x) ^ 2 - 3))

noncomputable def h6 (u : ℝ) : ℝ := h6Log (Real.exp u)

noncomputable def H6 (s : ℂ) : ℂ :=
  32 * (s - 1) * riemannZeta s /
    ((s + 2) * (s + 4) * (s + 6) * (s + 8) * (s + 10))

noncomputable def a6 (theta : ℝ) : ℝ :=
  2 / 45 - (4 / 3) * theta ^ 2 * (1 - theta) ^ 2

noncomputable def h6IntegerValue (N : ℕ) : ℝ :=
  (((N : ℝ) - 1) * ((N : ℝ) + 1) * (2 * (N : ℝ) - 5) *
      (2 * (N : ℝ) - 1) * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 5)) /
    (360 * (N : ℝ) ^ 9)

noncomputable def isBigOAtTopNat (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → |f N| ≤ C * |g N|

noncomputable def h6Remainder (theta : ℝ) (N : ℕ) : ℝ :=
  h6 (Real.log ((N : ℝ) + theta)) -
    a6 theta / (N : ℝ) ^ 3

noncomputable def h6SignChangeClaim : Prop :=
  (∀ N : ℕ, 0 < N →
    h6 (Real.log (N : ℝ)) = h6IntegerValue N) ∧
  h6 (Real.log (2 : ℝ)) < 0 ∧
  (∀ N : ℕ, 3 ≤ N → 0 < h6 (Real.log (N : ℝ))) ∧
  (∀ theta : ℝ, theta ∈ Set.Ico (0 : ℝ) 1 →
    isBigOAtTopNat (h6Remainder theta)
      (fun N : ℕ => 1 / (N : ℝ) ^ 4)) ∧
  0 < a6 0 ∧
  a6 (1 / 2 : ℝ) < 0 ∧
  (∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    h6 (Real.log ((N : ℝ) + 1 / 2)) < 0 ∧
    0 < h6 (Real.log ((N : ℝ) + 1)))

end MathlibPlus.Open.Analysis
