import Mathlib

namespace MathlibPlus.Algebra.Claim16744

/--
The exact polynomial and altered log-concavity slack core of the admitted
length-two/length-three broom claim.  The coefficients below are the actual
coefficients of the displayed centre-decomposition polynomial. This theorem
records the exact low-rank algebraic core; the source proof's real-rootedness
and inherited all-rank tail argument are separate.
-/
theorem alteredSlacks_claim16744 (r : ℕ) :
    let I_C_r : Polynomial ℚ :=
      (1 + Polynomial.X) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
        Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)
    let c₀ : ℚ := I_C_r.coeff 0
    let c₁ : ℚ := I_C_r.coeff 1
    let c₂ : ℚ := I_C_r.coeff 2
    let c₃ : ℚ := I_C_r.coeff 3
    let c₄ : ℚ := I_C_r.coeff 4
    let c₅ : ℚ := I_C_r.coeff 5
    (c₀ = 1 ∧
      c₁ = (r : ℚ) + 6 ∧
      c₂ = ((r : ℚ) ^ 2 + 9 * r + 20) / 2 ∧
      c₃ = ((r : ℚ) ^ 3 + 12 * (r : ℚ) ^ 2 + 29 * r + 24) / 6 ∧
      c₄ = ((r : ℚ) ^ 4 + 14 * (r : ℚ) ^ 3 + 35 * (r : ℚ) ^ 2 - 2 * r) / 24 ∧
      c₅ = ((r : ℚ) ^ 5 + 15 * (r : ℚ) ^ 4 + 25 * (r : ℚ) ^ 3 -
        75 * (r : ℚ) ^ 2 + 34 * r) / 120) ∧
    ((c₁ ^ 2 - c₀ * c₂ =
        ((r : ℚ) ^ 2 + 15 * r + 52) / 2) ∧
      0 < c₁ ^ 2 - c₀ * c₂) ∧
    ((c₂ ^ 2 - c₁ * c₃ =
        ((r : ℚ) ^ 4 + 18 * (r : ℚ) ^ 3 + 161 * (r : ℚ) ^ 2 +
          684 * r + 912) / 12) ∧
      0 < c₂ ^ 2 - c₁ * c₃) ∧
    ((c₃ ^ 2 - c₂ * c₄ =
        ((r : ℚ) ^ 6 + 27 * (r : ℚ) ^ 5 + 265 * (r : ℚ) ^ 4 +
          1197 * (r : ℚ) ^ 3 + 3622 * (r : ℚ) ^ 2 + 5688 * r + 2304) / 144) ∧
      0 < c₃ ^ 2 - c₂ * c₄) ∧
    ((c₄ ^ 2 - c₃ * c₅ =
        (r : ℚ) / 2880 * ((r : ℚ) ^ 7 + 32 * (r : ℚ) ^ 6 +
          394 * (r : ℚ) ^ 5 + 2144 * (r : ℚ) ^ 4 + 4969 * (r : ℚ) ^ 3 +
          3968 * (r : ℚ) ^ 2 + 3276 * r - 3264)) ∧
      0 ≤ c₄ ^ 2 - c₃ * c₅) := by
  dsimp
  have choose2_formula : ∀ n : ℕ, (n.choose 2 : ℚ) =
      ((n : ℚ) * ((n : ℚ) - 1)) / 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ n 1]
      simp only [Nat.cast_add, Nat.choose_one_right]
      rw [ih]
      ring
  have choose3_formula : ∀ n : ℕ, (n.choose 3 : ℚ) =
      ((n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2)) / 6 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ n 2]
      simp only [Nat.cast_add]
      change (n.choose 2 : ℚ) + (n.choose 3 : ℚ) = _
      rw [choose2_formula, ih]
      ring
  have choose4_formula : ∀ n : ℕ, (n.choose 4 : ℚ) =
      ((n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3)) / 24 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ n 3]
      simp only [Nat.cast_add]
      change (n.choose 3 : ℚ) + (n.choose 4 : ℚ) = _
      rw [choose3_formula, ih]
      ring
  have choose5_formula : ∀ n : ℕ, (n.choose 5 : ℚ) =
      ((n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) *
        ((n : ℚ) - 4)) / 120 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ n 4]
      simp only [Nat.cast_add]
      change (n.choose 4 : ℚ) + (n.choose 5 : ℚ) = _
      rw [choose4_formula, ih]
      ring
  have hfactor :
      ((1 + 2 * Polynomial.X : Polynomial ℚ) *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2)) =
        1 + 5 * Polynomial.X + 7 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 := by
    ring
  have hcorrection :
      (Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X) : Polynomial ℚ) =
        Polynomial.X + 3 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 := by
    ring
  have hcoeff :
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
          Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)).coeff 0 = 1 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
          Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)).coeff 1 =
        (r : ℚ) + 6 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
          Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)).coeff 2 =
        ((r : ℚ) ^ 2 + 9 * r + 20) / 2 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
          Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)).coeff 3 =
        ((r : ℚ) ^ 3 + 12 * (r : ℚ) ^ 2 + 29 * r + 24) / 6 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
          Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)).coeff 4 =
        ((r : ℚ) ^ 4 + 14 * (r : ℚ) ^ 3 + 35 * (r : ℚ) ^ 2 - 2 * r) / 24 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) +
          Polynomial.X * (1 + Polynomial.X) * (1 + 2 * Polynomial.X)).coeff 5 =
        ((r : ℚ) ^ 5 + 15 * (r : ℚ) ^ 4 + 25 * (r : ℚ) ^ 3 -
          75 * (r : ℚ) ^ 2 + 34 * r) / 120 := by
    have hproduct :
        ((1 + Polynomial.X : Polynomial ℚ) ^ r *
            (1 + 2 * Polynomial.X) * (1 + 3 * Polynomial.X + Polynomial.X ^ 2)) =
          (1 + Polynomial.X : Polynomial ℚ) ^ r *
            (1 + 5 * Polynomial.X + 7 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3) := by
      rw [mul_assoc, hfactor]
    rw [hproduct, hcorrection]
    simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_one,
      Polynomial.coeff_one_add_X_pow, Polynomial.coeff_X_one,
      Polynomial.coeff_X_of_ne_one, choose2_formula, choose3_formula,
      choose4_formula, choose5_formula,
      Finset.HasAntidiagonal.antidiagonal] <;> ring_nf <;> simp
  rcases hcoeff with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  have hr : (0 : ℚ) ≤ (r : ℚ) := by positivity
  have hs1 : 0 < ((r : ℚ) ^ 2 + 15 * r + 52) / 2 := by positivity
  have hs2 : 0 < ((r : ℚ) ^ 4 + 18 * (r : ℚ) ^ 3 + 161 * (r : ℚ) ^ 2 +
      684 * r + 912) / 12 := by positivity
  have hs3 : 0 < ((r : ℚ) ^ 6 + 27 * (r : ℚ) ^ 5 + 265 * (r : ℚ) ^ 4 +
      1197 * (r : ℚ) ^ 3 + 3622 * (r : ℚ) ^ 2 + 5688 * r + 2304) / 144 := by
    positivity
  have hs4 : 0 ≤ (r : ℚ) / 2880 * ((r : ℚ) ^ 7 + 32 * (r : ℚ) ^ 6 +
      394 * (r : ℚ) ^ 5 + 2144 * (r : ℚ) ^ 4 + 4969 * (r : ℚ) ^ 3 +
      3968 * (r : ℚ) ^ 2 + 3276 * r - 3264) := by
    by_cases hz : r = 0
    · simp [hz]
    · have hr1 : (1 : ℚ) ≤ (r : ℚ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
      have hlin : 0 ≤ 3276 * (r : ℚ) - 3264 := by nlinarith
      have hq2 : 0 ≤ (r : ℚ) ^ 2 := by positivity
      have hq3 : 0 ≤ (r : ℚ) ^ 3 := by positivity
      have hq4 : 0 ≤ (r : ℚ) ^ 4 := by positivity
      have hq5 : 0 ≤ (r : ℚ) ^ 5 := by positivity
      have hq6 : 0 ≤ (r : ℚ) ^ 6 := by positivity
      have hq7 : 0 ≤ (r : ℚ) ^ 7 := by positivity
      have hpoly : 0 ≤ (r : ℚ) ^ 7 + 32 * (r : ℚ) ^ 6 +
          394 * (r : ℚ) ^ 5 + 2144 * (r : ℚ) ^ 4 + 4969 * (r : ℚ) ^ 3 +
          3968 * (r : ℚ) ^ 2 + 3276 * r - 3264 := by
        nlinarith
      positivity
  simp only [h₀, h₁, h₂, h₃, h₄, h₅]
  constructor
  · simp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · ring
      · nlinarith [hs1]
    · constructor
      · ring
      · calc
          0 < ((r : ℚ) ^ 4 + 18 * (r : ℚ) ^ 3 + 161 * (r : ℚ) ^ 2 +
              684 * r + 912) / 12 := hs2
          _ = (((r : ℚ) ^ 2 + 9 * r + 20) / 2) ^ 2 -
              ((r : ℚ) + 6) *
                (((r : ℚ) ^ 3 + 12 * (r : ℚ) ^ 2 + 29 * r + 24) / 6) := by ring
    · constructor
      · ring
      · calc
          0 < ((r : ℚ) ^ 6 + 27 * (r : ℚ) ^ 5 + 265 * (r : ℚ) ^ 4 +
              1197 * (r : ℚ) ^ 3 + 3622 * (r : ℚ) ^ 2 + 5688 * r + 2304) / 144 := hs3
          _ = (((r : ℚ) ^ 3 + 12 * (r : ℚ) ^ 2 + 29 * r + 24) / 6) ^ 2 -
              ((r : ℚ) ^ 2 + 9 * r + 20) / 2 *
                (((r : ℚ) ^ 4 + 14 * (r : ℚ) ^ 3 + 35 * (r : ℚ) ^ 2 - 2 * r) / 24) := by ring
    · constructor
      · ring
      · calc
          0 ≤ (r : ℚ) / 2880 * ((r : ℚ) ^ 7 + 32 * (r : ℚ) ^ 6 +
              394 * (r : ℚ) ^ 5 + 2144 * (r : ℚ) ^ 4 + 4969 * (r : ℚ) ^ 3 +
              3968 * (r : ℚ) ^ 2 + 3276 * r - 3264) := hs4
          _ = (((r : ℚ) ^ 4 + 14 * (r : ℚ) ^ 3 + 35 * (r : ℚ) ^ 2 - 2 * r) / 24) ^ 2 -
              ((r : ℚ) ^ 3 + 12 * (r : ℚ) ^ 2 + 29 * r + 24) / 6 *
                (((r : ℚ) ^ 5 + 15 * (r : ℚ) ^ 4 + 25 * (r : ℚ) ^ 3 -
                  75 * (r : ℚ) ^ 2 + 34 * r) / 120) := by ring

end MathlibPlus.Algebra.Claim16744
