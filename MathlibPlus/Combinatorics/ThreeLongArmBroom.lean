import Mathlib

namespace MathlibPlus.Combinatorics

/--
The five altered log-concavity slacks from the source's three-long-arm
broom.  `I_G_r` is the source centre-decomposition independence polynomial;
the `gₖ` in the proposition are its actual coefficients, not detached
reported values.
-/
theorem alteredSlacks_claim48189 (r : ℕ) :
    let I_G_r : Polynomial ℚ :=
      (1 + Polynomial.X) ^ r * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
        Polynomial.X * (1 + 2 * Polynomial.X) ^ 3
    let g₀ : ℚ := I_G_r.coeff 0
    let g₁ : ℚ := I_G_r.coeff 1
    let g₂ : ℚ := I_G_r.coeff 2
    let g₃ : ℚ := I_G_r.coeff 3
    let g₄ : ℚ := I_G_r.coeff 4
    let g₅ : ℚ := I_G_r.coeff 5
    let g₆ : ℚ := I_G_r.coeff 6
    (g₁ ^ 2 - g₀ * g₂ = ((r : ℚ) ^ 2 + 23 * r + 128) / 2 ∧
      0 < g₁ ^ 2 - g₀ * g₂) ∧
    (g₂ ^ 2 - g₁ * g₃ =
        ((r : ℚ) ^ 4 + 34 * r ^ 3 + 509 * r ^ 2 + 3560 * r + 8712) / 12 ∧
      0 < g₂ ^ 2 - g₁ * g₃) ∧
    (g₃ ^ 2 - g₂ * g₄ =
        ((r : ℚ) ^ 6 + 51 * r ^ 5 + 1009 * r ^ 4 + 10245 * r ^ 3 +
            62134 * r ^ 2 + 207792 * r + 270864) / 144 ∧
      0 < g₃ ^ 2 - g₂ * g₄) ∧
    (g₄ ^ 2 - g₃ * g₅ =
        ((r : ℚ) ^ 8 + 64 * r ^ 7 + 1690 * r ^ 6 + 23272 * r ^ 5 +
            180049 * r ^ 4 + 825256 * r ^ 3 + 2394420 * r ^ 2 +
            3962448 * r + 2681280) / 2880 ∧
      0 < g₄ ^ 2 - g₃ * g₅) ∧
    (g₅ ^ 2 - g₄ * g₆ =
        ((r : ℚ) ^ 10 + 75 * r ^ 9 + 2340 * r ^ 8 + 39150 * r ^ 7 +
            383373 * r ^ 6 + 2244195 * r ^ 5 + 7786310 * r ^ 4 +
            15836100 * r ^ 3 + 18784776 * r ^ 2 + 10910880 * r +
            3715200) / 86400 ∧
      0 < g₅ ^ 2 - g₄ * g₆) := by
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
  have choose6_formula : ∀ n : ℕ, (n.choose 6 : ℚ) =
      ((n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) *
        ((n : ℚ) - 4) * ((n : ℚ) - 5)) / 720 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ n 5]
      simp only [Nat.cast_add]
      change (n.choose 5 : ℚ) + (n.choose 6 : ℚ) = _
      rw [choose5_formula, ih]
      ring
  have hbase :
      (1 + 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ 3 =
        1 + 9 * Polynomial.X + 30 * Polynomial.X ^ 2 +
          45 * Polynomial.X ^ 3 + 30 * Polynomial.X ^ 4 +
          9 * Polynomial.X ^ 5 + Polynomial.X ^ 6 := by
    ring
  have hleaf :
      Polynomial.X * (1 + 2 * Polynomial.X : Polynomial ℚ) ^ 3 =
        Polynomial.X + 6 * Polynomial.X ^ 2 + 12 * Polynomial.X ^ 3 +
          8 * Polynomial.X ^ 4 := by
    ring
  have hcoeff :
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 0 = 1 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 1 =
        (r : ℚ) + 10 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 2 =
        ((r : ℚ) + 8) * ((r : ℚ) + 9) / 2 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 3 =
        ((r : ℚ)^3 + 24 * (r : ℚ)^2 + 155 * (r : ℚ) + 342) / 6 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 4 =
        ((r : ℚ)^4 + 30 * (r : ℚ)^3 + 263 * (r : ℚ)^2 +
          786 * (r : ℚ) + 912) / 24 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 5 =
        ((r : ℚ)^5 + 35 * (r : ℚ)^4 + 365 * (r : ℚ)^3 +
          1345 * (r : ℚ)^2 + 1854 * (r : ℚ) + 1080) / 120 ∧
      ((1 + Polynomial.X : Polynomial ℚ) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 +
          Polynomial.X * (1 + 2 * Polynomial.X) ^ 3).coeff 6 =
        ((r : ℚ)^6 + 39 * (r : ℚ)^5 + 445 * (r : ℚ)^4 +
          1665 * (r : ℚ)^3 + 2074 * (r : ℚ)^2 +
          2256 * (r : ℚ) + 720) / 720 := by
    rw [hbase, hleaf]
    simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_one,
      Polynomial.coeff_one_add_X_pow, Polynomial.coeff_X_one,
      Polynomial.coeff_X_of_ne_one, choose2_formula, choose3_formula,
      choose4_formula, choose5_formula, choose6_formula,
      Finset.HasAntidiagonal.antidiagonal] <;> ring_nf <;> simp
  rcases hcoeff with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆]
  have hr : (0 : ℚ) ≤ (r : ℚ) := by positivity
  constructor
  · constructor
    · ring
    · nlinarith [hr]
  constructor
  · constructor
    · ring
    · nlinarith [hr]
  constructor
  · constructor
    · ring
    · nlinarith [hr]
  constructor
  · constructor
    · ring
    · calc
        0 < ((r : ℚ) ^ 8 + 64 * (r : ℚ) ^ 7 + 1690 * (r : ℚ) ^ 6 +
            23272 * (r : ℚ) ^ 5 + 180049 * (r : ℚ) ^ 4 +
            825256 * (r : ℚ) ^ 3 + 2394420 * (r : ℚ) ^ 2 +
            3962448 * (r : ℚ) + 2681280) / 2880 := by positivity
        _ =
          (((r : ℚ) ^ 4 + 30 * (r : ℚ) ^ 3 + 263 * (r : ℚ) ^ 2 +
              786 * (r : ℚ) + 912) / 24) ^ 2 -
            (((r : ℚ) ^ 3 + 24 * (r : ℚ) ^ 2 + 155 * (r : ℚ) + 342) / 6) *
              (((r : ℚ) ^ 5 + 35 * (r : ℚ) ^ 4 + 365 * (r : ℚ) ^ 3 +
                1345 * (r : ℚ) ^ 2 + 1854 * (r : ℚ) + 1080) / 120) := by ring
  · constructor
    · ring
    · calc
        0 < ((r : ℚ) ^ 10 + 75 * (r : ℚ) ^ 9 + 2340 * (r : ℚ) ^ 8 +
            39150 * (r : ℚ) ^ 7 + 383373 * (r : ℚ) ^ 6 +
            2244195 * (r : ℚ) ^ 5 + 7786310 * (r : ℚ) ^ 4 +
            15836100 * (r : ℚ) ^ 3 + 18784776 * (r : ℚ) ^ 2 +
            10910880 * (r : ℚ) + 3715200) / 86400 := by positivity
        _ =
          (((r : ℚ) ^ 5 + 35 * (r : ℚ) ^ 4 + 365 * (r : ℚ) ^ 3 +
              1345 * (r : ℚ) ^ 2 + 1854 * (r : ℚ) + 1080) / 120) ^ 2 -
            (((r : ℚ) ^ 4 + 30 * (r : ℚ) ^ 3 + 263 * (r : ℚ) ^ 2 +
                786 * (r : ℚ) + 912) / 24) *
              (((r : ℚ) ^ 6 + 39 * (r : ℚ) ^ 5 + 445 * (r : ℚ) ^ 4 +
                1665 * (r : ℚ) ^ 3 + 2074 * (r : ℚ) ^ 2 +
                2256 * (r : ℚ) + 720) / 720) := by ring

end MathlibPlus.Combinatorics
