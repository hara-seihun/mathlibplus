import Mathlib

namespace MathlibPlus.Open

noncomputable def unsampledCellNullspace_claim2475 : Prop :=
  ∀ (h : ℝ → ℝ),
    (∀ x : ℝ, h x ≠ 0 → x ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ u → h ((n : ℝ) * u) = 0) ∧
        (∀ (g : ℝ → ℝ) (u : ℝ),
          1 ≤ u →
            (∑' n : {n : ℕ // 0 < n},
                (g + h) ((n : ℝ) * u)) =
              ∑' n : {n : ℕ // 0 < n}, g ((n : ℝ) * u))

end MathlibPlus.Open
