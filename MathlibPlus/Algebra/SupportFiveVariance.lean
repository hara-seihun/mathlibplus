import Mathlib

namespace MathlibPlus.Algebra.SupportFiveVariance

/-!
Kernel-checked algebraic consequences of admitted claim 51538 (packet R-4309).
The source's rooted-row, type-reduction, monicity, and injectivity interfaces are
not formalized here; the displayed symmetric identities and the integral
four-divisibility consequence are.
-/

/-- The six pairwise squared differences are the energy of the three
nontrivial channels of the four-by-four Sylvester Hadamard transform. -/
theorem hadamard_row_variance_claim51538 (A₁ A₂ A₃ A₄ : ℚ) :
    let D₁ : ℚ := (A₁ - A₂ + A₃ - A₄) / 2
    let D₂ : ℚ := (A₁ + A₂ - A₃ - A₄) / 2
    let D₃ : ℚ := (A₁ - A₂ - A₃ + A₄) / 2
    (A₁ - A₂) ^ 2 + (A₁ - A₃) ^ 2 + (A₁ - A₄) ^ 2 +
        (A₂ - A₃) ^ 2 + (A₂ - A₄) ^ 2 + (A₃ - A₄) ^ 2 =
      4 * (D₁ ^ 2 + D₂ ^ 2 + D₃ ^ 2) := by
  dsimp
  ring

/-- With the displayed support-five parent relation, the same variance has the
claimed coefficient-weighted square expression. -/
theorem hadamard_parent_identity_claim51538
    (e₀ F₀ c₁ c₂ c₃ c₄ F₁ F₂ F₃ F₄ : ℚ)
    (h : e₀ * F₀ + c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = 0) :
    let A₁ : ℚ := c₁ * F₁
    let A₂ : ℚ := c₂ * F₂
    let A₃ : ℚ := c₃ * F₃
    let A₄ : ℚ := c₄ * F₄
    (A₁ - A₂) ^ 2 + (A₁ - A₃) ^ 2 + (A₁ - A₄) ^ 2 +
        (A₂ - A₃) ^ 2 + (A₂ - A₄) ^ 2 + (A₃ - A₄) ^ 2 =
      4 * (c₁ ^ 2 * F₁ ^ 2 + c₂ ^ 2 * F₂ ^ 2 +
        c₃ ^ 2 * F₃ ^ 2 + c₄ ^ 2 * F₄ ^ 2) - e₀ ^ 2 * F₀ ^ 2 := by
  dsimp
  have hsum : c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = -e₀ * F₀ := by
    linarith [h]
  calc
    (c₁ * F₁ - c₂ * F₂) ^ 2 + (c₁ * F₁ - c₃ * F₃) ^ 2 +
          (c₁ * F₁ - c₄ * F₄) ^ 2 + (c₂ * F₂ - c₃ * F₃) ^ 2 +
          (c₂ * F₂ - c₄ * F₄) ^ 2 + (c₃ * F₃ - c₄ * F₄) ^ 2 =
        4 * ((c₁ * F₁) ^ 2 + (c₂ * F₂) ^ 2 +
          (c₃ * F₃) ^ 2 + (c₄ * F₄) ^ 2) -
          (c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄) ^ 2 := by ring
    _ = 4 * (c₁ ^ 2 * F₁ ^ 2 + c₂ ^ 2 * F₂ ^ 2 +
          c₃ ^ 2 * F₃ ^ 2 + c₄ ^ 2 * F₄ ^ 2) - e₀ ^ 2 * F₀ ^ 2 := by
      rw [hsum]
      ring

/-- The support-five variance is divisible by four over the integers when the
central coefficient is even and the parent relation holds.  The oddness of the
four `cᵢ` in the source is retained as explicit hypotheses, although this
particular divisibility consequence only uses the evenness of `e₀`. -/
theorem integral_variance_divisible_four_claim51538
    (e₀ F₀ c₁ c₂ c₃ c₄ F₁ F₂ F₃ F₄ : ℤ)
    (he₀ : ∃ k : ℤ, e₀ = 2 * k)
    (hc₁ : ∃ k : ℤ, c₁ = 2 * k + 1)
    (hc₂ : ∃ k : ℤ, c₂ = 2 * k + 1)
    (hc₃ : ∃ k : ℤ, c₃ = 2 * k + 1)
    (hc₄ : ∃ k : ℤ, c₄ = 2 * k + 1)
    (h : e₀ * F₀ + c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = 0) :
    ∃ q : ℤ,
      (c₁ * F₁ - c₂ * F₂) ^ 2 + (c₁ * F₁ - c₃ * F₃) ^ 2 +
          (c₁ * F₁ - c₄ * F₄) ^ 2 + (c₂ * F₂ - c₃ * F₃) ^ 2 +
          (c₂ * F₂ - c₄ * F₄) ^ 2 + (c₃ * F₃ - c₄ * F₄) ^ 2 = 4 * q := by
  rcases he₀ with ⟨k, hk⟩
  have hsum : c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = -(2 * k) * F₀ := by
    calc
      c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄ = -e₀ * F₀ := by
        linarith [h]
      _ = -(2 * k) * F₀ := by rw [hk]
  refine ⟨(c₁ * F₁) ^ 2 + (c₂ * F₂) ^ 2 +
      (c₃ * F₃) ^ 2 + (c₄ * F₄) ^ 2 - (k * F₀) ^ 2, ?_⟩
  calc
    (c₁ * F₁ - c₂ * F₂) ^ 2 + (c₁ * F₁ - c₃ * F₃) ^ 2 +
          (c₁ * F₁ - c₄ * F₄) ^ 2 + (c₂ * F₂ - c₃ * F₃) ^ 2 +
          (c₂ * F₂ - c₄ * F₄) ^ 2 + (c₃ * F₃ - c₄ * F₄) ^ 2 =
        4 * ((c₁ * F₁) ^ 2 + (c₂ * F₂) ^ 2 +
          (c₃ * F₃) ^ 2 + (c₄ * F₄) ^ 2) -
          (c₁ * F₁ + c₂ * F₂ + c₃ * F₃ + c₄ * F₄) ^ 2 := by ring
    _ = 4 * ((c₁ * F₁) ^ 2 + (c₂ * F₂) ^ 2 +
          (c₃ * F₃) ^ 2 + (c₄ * F₄) ^ 2 - (k * F₀) ^ 2) := by
      rw [hsum]
      ring

end MathlibPlus.Algebra.SupportFiveVariance
