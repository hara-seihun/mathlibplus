import Mathlib

namespace MathlibPlus.Analysis.SingleSpike

noncomputable section

/-- The scale factor in the admitted single-spike family. Real powers are used
for the fractional exponents in the source formula. -/
def height (x : ℝ) (N : ℕ) : ℝ :=
  Real.exp (x / 2) * Real.sqrt (Nat.factorial N : ℝ) *
    x ^ (-(N : ℝ) / 2) * (N : ℝ) ^ (-(1 : ℝ) / 4)

/-- The coefficient sequence supported at the single index `N`. -/
def coefficient (x : ℝ) (N k : ℕ) : ℝ :=
  if k = N then height x N else 0

/-- The polynomial displayed in the admitted claim, over the complex numbers. -/
def polynomial (x : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (height x N : ℂ) * z ^ N / (Nat.factorial N : ℂ)

theorem coefficient_eq_zero_of_ne {x : ℝ} {N k : ℕ} (h : k ≠ N) :
    coefficient x N k = 0 := by
  simp [coefficient, h]

theorem coefficient_at_index {x : ℝ} {N : ℕ} :
    coefficient x N N = height x N := by
  simp [coefficient]

theorem height_pos {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : 1 ≤ N) :
    0 < height x N := by
  dsimp [height]
  positivity

end

end MathlibPlus.Analysis.SingleSpike

namespace MathlibPlus.Analysis.SingleSpike

/-- The single-spike EGF has only one nonzero consecutive Turan bracket. -/
theorem singleSpike_turanBracket_claim15687
    (c : ℝ) (N n : ℕ) (hN : 1 ≤ N) :
    let h : ℝ := Real.sqrt (Nat.factorial N : ℝ) * c ^ N
    let u : ℕ → ℝ := fun k => if k = N then h else 0
    u n * u (n + 2) - u (n + 1) ^ 2 =
      if n = N - 1 then
        -(Nat.factorial N : ℝ) * c ^ (2 * N) else 0 := by
  dsimp
  classical
  by_cases hn : n = N - 1
  · have hNm : N - 1 ≠ N := by omega
    have hNp : N - 1 + 2 ≠ N := by omega
    have hsqrt : (Real.sqrt (Nat.factorial N : ℝ)) ^ 2 =
        (Nat.factorial N : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    simp [hn, hNm, hNp, Nat.sub_add_cancel hN]
    rw [mul_pow, hsqrt]
    have hpow : (c ^ N) ^ 2 = c ^ (2 * N) := by
      calc
        (c ^ N) ^ 2 = c ^ (N * 2) := (pow_mul c N 2).symm
        _ = c ^ (2 * N) := by congr 1 <;> omega
    rw [hpow]
  · by_cases h0 : n = N
    · have h1 : n + 1 ≠ N := by omega
      have h2 : n + 2 ≠ N := by omega
      have hNm : N ≠ N - 1 := by omega
      simp [hn, h0, h1, h2, hNm]
    · by_cases h2 : n + 2 = N
      · have h1 : n + 1 ≠ N := by omega
        have hNm : N ≠ N - 1 := by omega
        simp [hn, h0, h1, h2, hNm]
      · by_cases h1 : n + 1 = N
        · exfalso
          apply hn
          omega
        · have hNm : N ≠ N - 1 := by omega
          simp [hn, h0, h1, h2, hNm]

end MathlibPlus.Analysis.SingleSpike
