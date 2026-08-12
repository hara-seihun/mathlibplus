import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- The exact angular phase maximum from the packet, with `√(√x)` used
    for the source notation `x ^ (1 / 4)`. -/
theorem claim4244_phaseMaximum
    {x t r : ℝ} (hx : 0 < x) (ht : 0 ≤ t) (hr : 0 < r) :
    let a := Real.sqrt x
    let b := Real.sqrt a
    let c := Real.sqrt (r * t)
    let q₀ := Real.sqrt t / (2 * b * Real.sqrt r)
    let Φ := fun q : ℝ =>
      -r ^ 2 + 2 * a * r * (1 - 2 * q ^ 2) + 4 * b * c * q
    (∀ q : ℝ, Φ q ≤ Φ q₀) ∧
      (if r ≤ t / (4 * a) then
        (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
          Φ q ≤ -r ^ 2 - 2 * a * r + 4 * b * c) ∧
          Φ 1 = -r ^ 2 - 2 * a * r + 4 * b * c
      else
        (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
          Φ q ≤ -r ^ 2 + 2 * a * r + t) ∧
          Φ q₀ = -r ^ 2 + 2 * a * r + t) := by
  dsimp
  let a : ℝ := Real.sqrt x
  let b : ℝ := Real.sqrt a
  let c : ℝ := Real.sqrt (r * t)
  let q₀ : ℝ := Real.sqrt t / (2 * b * Real.sqrt r)
  let Φ : ℝ → ℝ := fun q =>
    -r ^ 2 + 2 * a * r * (1 - 2 * q ^ 2) + 4 * b * c * q
  change
    (∀ q : ℝ, Φ q ≤ Φ q₀) ∧
      (if r ≤ t / (4 * a) then
        (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
          Φ q ≤ -r ^ 2 - 2 * a * r + 4 * b * c) ∧
          Φ 1 = -r ^ 2 - 2 * a * r + 4 * b * c
      else
        (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
          Φ q ≤ -r ^ 2 + 2 * a * r + t) ∧
          Φ q₀ = -r ^ 2 + 2 * a * r + t)
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 hx
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 ha
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hrt : c = Real.sqrt r * Real.sqrt t := by
    dsimp [c]
    rw [Real.sqrt_mul (le_of_lt hr)]
  have hbsq : b ^ 2 = a := by
    dsimp [b]
    exact Real.sq_sqrt (le_of_lt ha)
  have hrsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  have htsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have hq0_nonneg : 0 ≤ q₀ := by
    dsimp [q₀]
    positivity
  have hq0sq : q₀ ^ 2 = t / (4 * a * r) := by
    dsimp [q₀]
    rw [div_pow, htsq]
    have hden : 2 * b * Real.sqrt r ≠ 0 := by positivity
    field_simp [hden]
    rw [hbsq, hrsq]
    ring
  have hq0lin : 2 * a * r * q₀ = b * c := by
    rw [hrt]
    dsimp [q₀]
    have hden : 2 * b * Real.sqrt r ≠ 0 := by positivity
    field_simp [hden]
    rw [hbsq, hrsq]
    ring
  have hlin : 4 * b * c = 8 * a * r * q₀ := by
    nlinarith [hq0lin]
  have hdiff (q : ℝ) : Φ q₀ - Φ q = 4 * a * r * (q₀ - q) ^ 2 := by
    dsimp [Φ]
    rw [hlin]
    ring
  have hunconstrained : ∀ q : ℝ, Φ q ≤ Φ q₀ := by
    intro q
    have hnonneg : 0 ≤ 4 * a * r * (q₀ - q) ^ 2 := by positivity
    nlinarith [hdiff q]
  refine ⟨hunconstrained, ?_⟩
  by_cases hcase : r ≤ t / (4 * a)
  · have hdena : 0 < 4 * a := by positivity
    have hdenar : 0 < 4 * a * r := by positivity
    have htr : 4 * a * r ≤ t := by
      have h := (le_div_iff₀ hdena).mp hcase
      nlinarith
    have hq0ge : 1 ≤ q₀ := by
      have hsq : 1 ≤ q₀ ^ 2 := by
        rw [hq0sq]
        apply (le_div_iff₀ hdenar).2
        nlinarith
      nlinarith [hq0_nonneg]
    have hdiff_one (q : ℝ) :
        Φ 1 - Φ q = 4 * a * r * (1 - q) * (2 * q₀ - 1 - q) := by
      dsimp [Φ]
      rw [hlin]
      ring
    have hbound : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
        Φ q ≤ -r ^ 2 - 2 * a * r + 4 * b * c := by
      intro q hq hq1
      have hprod : 0 ≤ 4 * a * r * (1 - q) * (2 * q₀ - 1 - q) := by
        have h₁ : 0 ≤ 4 * a * r := by positivity
        have h₂ : 0 ≤ 1 - q := by linarith
        have h₃ : 0 ≤ 2 * q₀ - 1 - q := by linarith
        positivity
      have hone : Φ 1 = -r ^ 2 - 2 * a * r + 4 * b * c := by
        dsimp [Φ]
        ring
      rw [← hone]
      nlinarith [hdiff_one q]
    have hone : Φ 1 = -r ^ 2 - 2 * a * r + 4 * b * c := by
      dsimp [Φ]
      ring
    rw [if_pos hcase]
    exact ⟨hbound, hone⟩
  · have hdena : 0 < 4 * a := by positivity
    have hdenar : 0 < 4 * a * r := by positivity
    have hcase' : t / (4 * a) ≤ r := by
      have hlt : t / (4 * a) < r := lt_of_not_ge hcase
      exact le_of_lt hlt
    have htr : t ≤ 4 * a * r := by
      have h := (div_le_iff₀ hdena).mp hcase'
      nlinarith
    have hq0le : q₀ ≤ 1 := by
      have hsq : q₀ ^ 2 ≤ 1 := by
        rw [hq0sq]
        apply (div_le_iff₀ hdenar).2
        nlinarith
      nlinarith [hq0_nonneg]
    have hvalue_aux : Φ q₀ = -r ^ 2 + 2 * a * r + 4 * a * r * q₀ ^ 2 := by
      dsimp [Φ]
      rw [hlin]
      ring
    have hvalue : Φ q₀ = -r ^ 2 + 2 * a * r + t := by
      rw [hvalue_aux, hq0sq]
      field_simp
    have hbound : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
        Φ q ≤ -r ^ 2 + 2 * a * r + t := by
      intro q hq hq1
      nlinarith [hdiff q, hvalue]
    rw [if_neg hcase]
    exact ⟨hbound, hvalue⟩

end MathlibPlus.Analysis
