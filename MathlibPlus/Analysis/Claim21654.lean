import Mathlib

open Set

namespace MathlibPlus.Analysis.Claim21654

/-- Exact maximum of the scalar phase-side loss on the unit interval. -/
theorem exactPhaseSideScalarOptimization (C : ℝ) (hC : 0 ≤ C) :
    ∃ r : ℝ, r ∈ Icc 0 1 ∧
      (1 + C * Real.sqrt r) / (1 + r) =
        (1 + Real.sqrt (1 + C ^ 2)) / 2 ∧
      ∀ s : ℝ, s ∈ Icc 0 1 →
        (1 + C * Real.sqrt s) / (1 + s) ≤
          (1 + C * Real.sqrt r) / (1 + r) := by
  let D : ℝ := Real.sqrt (1 + C ^ 2)
  let t₀ : ℝ := C / (D + 1)
  let r₀ : ℝ := t₀ ^ 2
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact Real.sqrt_nonneg _
  have hDsq : D ^ 2 = 1 + C ^ 2 := by
    dsimp [D]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg C])
  have hD1 : 1 ≤ D := by
    nlinarith [hDsq, sq_nonneg (D - 1)]
  have hden : 0 < D + 1 := by linarith
  have hDC : C ≤ D := by
    nlinarith [hDsq]
  have ht0_nonneg : 0 ≤ t₀ := by
    dsimp [t₀]
    exact div_nonneg hC (le_of_lt hden)
  have ht0_le_one : t₀ ≤ 1 := by
    dsimp [t₀]
    apply (div_le_iff₀ hden).2
    linarith
  have hr₀_mem : r₀ ∈ Icc 0 1 := by
    constructor
    · dsimp [r₀]
      positivity
    · dsimp [r₀]
      nlinarith [sq_nonneg t₀]
  have hsqrt_r₀ : Real.sqrt r₀ = t₀ := by
    dsimp [r₀]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht0_nonneg]
  have ht0_eq : (1 + D) * t₀ = C := by
    dsimp [t₀]
    field_simp [ne_of_gt hden]
    ring
  have ht0_sq : (1 + D) * t₀ ^ 2 = D - 1 := by
    dsimp [t₀]
    field_simp [ne_of_gt hden]
    nlinarith [hDsq]
  have hvalue :
      (1 + C * Real.sqrt r₀) / (1 + r₀) = (1 + D) / 2 := by
    rw [hsqrt_r₀]
    have hdenr : 0 < 1 + r₀ := by
      dsimp [r₀]
      nlinarith [sq_nonneg t₀]
    apply (div_eq_iff (ne_of_gt hdenr)).2
    nlinarith [ht0_eq, ht0_sq]
  refine ⟨r₀, hr₀_mem, ?_, ?_⟩
  · simpa [D] using hvalue
  · intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    let u : ℝ := Real.sqrt s
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact Real.sqrt_nonneg _
    have husq : u ^ 2 = s := by
      dsimp [u]
      exact Real.sq_sqrt hs0
    have hu1 : u ≤ 1 := by
      nlinarith [husq]
    have hpoly : 0 ≤ (1 + D) * (u - t₀) ^ 2 := by
      positivity
    have hbound :
        (1 + C * Real.sqrt s) / (1 + s) ≤ (1 + D) / 2 := by
      have hden_s : 0 < 1 + s := by linarith
      apply (div_le_iff₀ hden_s).2
      dsimp [u] at husq hu0 hu1 hpoly ⊢
      nlinarith [hpoly, ht0_eq, ht0_sq]
    rw [hvalue]
    exact hbound

end MathlibPlus.Analysis.Claim21654
