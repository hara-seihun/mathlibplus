import Mathlib

namespace MathlibPlus.LinearAlgebra

/-!
# Corrected Hadamard frame

This file records the exact integer/rational core of admitted claim 51482.  The
four displayed `F₁, …, F₄` are the support-four entries; the oddness hypotheses
are retained even though the parity conclusion uses the even coefficient `e₀`
and the displayed relation directly.
-/

/-- The corrected Sylvester-Hadamard frame is integral, has the stated zeroth
coordinate, and satisfies the prime-free perpendicular-energy identity. -/
theorem correctedHadamardFrame_energy
    (e₀ F₀ F₁ F₂ F₃ F₄ c₁ c₂ c₃ c₄ : ℤ)
    (he : e₀ = 2 ∨ e₀ = 4 ∨ e₀ = 6)
    (_hc₁ : Odd c₁) (_hc₂ : Odd c₂) (_hc₃ : Odd c₃) (_hc₄ : Odd c₄)
    (hrel : e₀ * F₀ + c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = 0) :
    ∃ D₀ D₁ D₂ D₃ : ℤ,
      2 * D₀ = c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ ∧
      2 * D₁ = c₁ * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄ ∧
      2 * D₂ = c₁ * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄ ∧
      2 * D₃ = c₁ * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄ ∧
      D₀ = -(e₀ / 2) * F₀ ∧
      ((D₁ : ℚ)^2 + (D₂ : ℚ)^2 + (D₃ : ℚ)^2) =
        (c₁ : ℚ)^2 * (F₁ : ℚ)^2 + (c₂ : ℚ)^2 * (F₂ : ℚ)^2 +
          (c₃ : ℚ)^2 * (F₃ : ℚ)^2 + (c₄ : ℚ)^2 * (F₄ : ℚ)^2 -
          ((e₀ : ℚ)^2 / 4) * (F₀ : ℚ)^2 := by
  let D₀ : ℤ := (c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄) / 2
  let D₁ : ℤ := (c₁ * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄) / 2
  let D₂ : ℤ := (c₁ * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄) / 2
  let D₃ : ℤ := (c₁ * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄) / 2
  have hsum : c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = -(e₀ * F₀) := by
    linarith [hrel]
  have hframe :
      let d₀ := (c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄) / 2
      let d₁ := (c₁ * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄) / 2
      let d₂ := (c₁ * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄) / 2
      let d₃ := (c₁ * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄) / 2
      2 * d₀ = c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ ∧
      2 * d₁ = c₁ * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄ ∧
      2 * d₂ = c₁ * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄ ∧
      2 * d₃ = c₁ * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄ ∧
      d₀ = -(e₀ / 2) * F₀ := by
    rcases he with rfl | rfl | rfl <;> dsimp
    all_goals
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · rw [hsum]
        omega
  dsimp at hframe
  refine ⟨D₀, D₁, D₂, D₃, ?_⟩
  dsimp [D₀, D₁, D₂, D₃]
  constructor
  · exact hframe.1
  constructor
  · exact hframe.2.1
  constructor
  · exact hframe.2.2.1
  constructor
  · exact hframe.2.2.2.1
  constructor
  · exact hframe.2.2.2.2
  ·
    have h1 := congrArg (fun z : ℤ => (z : ℚ)) hframe.2.1
    have h2 := congrArg (fun z : ℤ => (z : ℚ)) hframe.2.2.1
    have h3 := congrArg (fun z : ℤ => (z : ℚ)) hframe.2.2.2.1
    have hrelq := congrArg (fun z : ℤ => (z : ℚ)) hrel
    norm_num at h1 h2 h3 hrelq
    have h1' : (((c₁ * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄) / 2 : ℤ) : ℚ) =
        ((c₁ : ℚ) * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄) / 2 := by
      linarith [h1]
    have h2' : (((c₁ * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄) / 2 : ℤ) : ℚ) =
        ((c₁ : ℚ) * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄) / 2 := by
      linarith [h2]
    have h3' : (((c₁ * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄) / 2 : ℤ) : ℚ) =
        ((c₁ : ℚ) * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄) / 2 := by
      linarith [h3]
    have hsumq : (c₁ : ℚ) * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ =
        -(e₀ * F₀) := by
      linarith [hrelq]
    rw [h1', h2', h3']
    calc
      ((c₁ * F₁ - c₂ * F₂ + c₃ * F₃ - c₄ * F₄) / 2)^2 +
            ((c₁ * F₁ + c₂ * F₂ - c₃ * F₃ - c₄ * F₄) / 2)^2 +
            ((c₁ * F₁ - c₂ * F₂ - c₃ * F₃ + c₄ * F₄) / 2)^2 =
          (c₁ : ℚ)^2 * F₁^2 + c₂^2 * F₂^2 + c₃^2 * F₃^2 + c₄^2 * F₄^2 -
            ((c₁ : ℚ) * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄)^2 / 4 := by ring
      _ = (c₁ : ℚ)^2 * F₁^2 + c₂^2 * F₂^2 + c₃^2 * F₃^2 + c₄^2 * F₄^2 -
            ((e₀ : ℚ) * F₀)^2 / 4 := by rw [hsumq]; ring
      _ = (c₁ : ℚ)^2 * F₁^2 + c₂^2 * F₂^2 + c₃^2 * F₃^2 + c₄^2 * F₄^2 -
            ((e₀ : ℚ)^2 / 4) * F₀^2 := by ring

end MathlibPlus.LinearAlgebra
