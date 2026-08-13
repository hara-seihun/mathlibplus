import Mathlib

namespace MathlibPlus.Combinatorics.Claim36301

theorem starCollarDeterminant_claim36301 (m : ℕ) (hm : 4 ≤ m) :
    Matrix.det (fun i j : Fin 2 =>
      match i, j with
      | 0, 0 => ((m - 1 : ℕ) : ℚ)
      | 0, 1 => (Nat.choose (m - 1) 2 : ℚ)
      | 1, 0 => ((m - 2 : ℕ) : ℚ)
      | 1, 1 => (Nat.choose (m - 2) 2 : ℚ)) =
      -(Nat.choose (m - 1) 2 : ℚ) := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
    match i, j with
    | 0, 0 => ((m - 1 : ℕ) : ℚ)
    | 0, 1 => (Nat.choose (m - 1) 2 : ℚ)
    | 1, 0 => ((m - 2 : ℕ) : ℚ)
    | 1, 1 => (Nat.choose (m - 2) 2 : ℚ)
  change A.det = _
  rw [Matrix.det_fin_two A]
  dsimp [A]
  simp only [Nat.cast_choose_two]
  rw [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega)]
  ring

theorem starCollarDeterminant_not_unit_claim36301 (m : ℕ) (hm : 4 ≤ m) :
    ¬ (Matrix.det (fun i j : Fin 2 =>
      match i, j with
      | 0, 0 => ((m - 1 : ℕ) : ℚ)
      | 0, 1 => (Nat.choose (m - 1) 2 : ℚ)
      | 1, 0 => ((m - 2 : ℕ) : ℚ)
      | 1, 1 => (Nat.choose (m - 2) 2 : ℚ)) = 1 ∨
      Matrix.det (fun i j : Fin 2 =>
      match i, j with
      | 0, 0 => ((m - 1 : ℕ) : ℚ)
      | 0, 1 => (Nat.choose (m - 1) 2 : ℚ)
      | 1, 0 => ((m - 2 : ℕ) : ℚ)
      | 1, 1 => (Nat.choose (m - 2) 2 : ℚ)) = -1) := by
  have hc : 3 ≤ Nat.choose (m - 1) 2 := by
    have hbase : 3 ≤ m - 1 := by omega
    have hmono := Nat.choose_mono 2 hbase
    norm_num at hmono ⊢
    exact hmono
  have hcq : (3 : ℚ) ≤ (Nat.choose (m - 1) 2 : ℚ) := by exact_mod_cast hc
  rw [starCollarDeterminant_claim36301 m hm]
  intro h
  rcases h with h | h <;> nlinarith

end MathlibPlus.Combinatorics.Claim36301
