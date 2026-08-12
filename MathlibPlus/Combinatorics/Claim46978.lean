import Mathlib

namespace MathlibPlus.Combinatorics.Claim46978

/-- The constant rational profile in the scalar relaxation satisfies the exact
consecutive-layer inequality from claim 46978.  The host weights are retained
as `M k = (n-k) * choose n k`; no cube-realizability assertion is added. -/
theorem constant_profile_witness (n : ℕ) (hn : 0 < n) :
    let q : Fin n → ℚ := fun _ => 7 / 10
    let M : Fin n → ℚ :=
      fun k => (((n - k.1) * Nat.choose n k.1 : ℕ) : ℚ)
    (∀ k : {k : Fin n // k.1 + 2 ≤ n},
      0 ≤ q k.1 ∧ q k.1 ≤ 1 ∧
        (q k.1)^2 * ((n - k.1.1 : ℕ) : ℚ) / ((n - k.1.1 - 1 : ℕ) : ℚ) +
            (q ⟨k.1.1 + 1, by have hk := k.2; omega⟩)^2 *
              ((k.1.1 + 2 : ℕ) : ℚ) / ((k.1.1 + 1 : ℕ) : ℚ) -
            q k.1 / ((n - k.1.1 - 1 : ℕ) : ℚ) -
            q ⟨k.1.1 + 1, by have hk := k.2; omega⟩ /
              ((k.1.1 + 1 : ℕ) : ℚ) ≤ 1) ∧
      (∑ i : Fin n, M i * q i) = (7 / 10 : ℚ) * ∑ i : Fin n, M i ∧
      (1 / 2 : ℚ) * ∑ i : Fin n, M i <
        ∑ i : Fin n, M i * q i := by
  dsimp
  constructor
  · intro k
    have hk := k.2
    have hnkm1 : 0 < n - k.1.1 - 1 := by omega
    have hkp1 : 0 < k.1.1 + 1 := by omega
    have hden₁ : (0 : ℚ) < ((n - k.1.1 - 1 : ℕ) : ℚ) := by positivity
    have hden₂ : (0 : ℚ) < ((k.1.1 + 1 : ℕ) : ℚ) := by positivity
    refine ⟨by norm_num, by norm_num, ?_⟩
    have hform :
        (7 / 10 : ℚ)^2 * ((n - k.1.1 : ℕ) : ℚ) / ((n - k.1.1 - 1 : ℕ) : ℚ) +
            (7 / 10 : ℚ)^2 * ((k.1.1 + 2 : ℕ) : ℚ) / ((k.1.1 + 1 : ℕ) : ℚ) -
            (7 / 10 : ℚ) / ((n - k.1.1 - 1 : ℕ) : ℚ) -
            (7 / 10 : ℚ) / ((k.1.1 + 1 : ℕ) : ℚ) =
          49 / 50 - (21 / 100 : ℚ) / ((n - k.1.1 - 1 : ℕ) : ℚ) -
            (21 / 100 : ℚ) / ((k.1.1 + 1 : ℕ) : ℚ) := by
      have hnk : n - k.1.1 = (n - k.1.1 - 1) + 1 := by omega
      have hnkc : ((n - k.1.1 : ℕ) : ℚ) = ((n - k.1.1 - 1 : ℕ) : ℚ) + 1 := by
        exact_mod_cast hnk
      have hkp : k.1.1 + 2 = (k.1.1 + 1) + 1 := by omega
      have hkpc : ((k.1.1 + 2 : ℕ) : ℚ) = ((k.1.1 + 1 : ℕ) : ℚ) + 1 := by
        exact_mod_cast hkp
      rw [hnkc, hkpc]
      field_simp
      ring
    rw [hform]
    have hnonneg₁ : (0 : ℚ) ≤ (21 / 100 : ℚ) / ((n - k.1.1 - 1 : ℕ) : ℚ) := by
      positivity
    have hnonneg₂ : (0 : ℚ) ≤ (21 / 100 : ℚ) / ((k.1.1 + 1 : ℕ) : ℚ) := by
      positivity
    linarith
  · constructor
    · rw [show (∑ i : Fin n,
          (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) * (7 / 10 : ℚ)) =
            ∑ i : Fin n, (7 / 10 : ℚ) *
              (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) by
          apply Finset.sum_congr rfl
          intro i hi
          ring]
      rw [Finset.mul_sum]
    · have hterm :
          (0 : ℚ) < (((n - (⟨0, hn⟩ : Fin n).1) *
            Nat.choose n (⟨0, hn⟩ : Fin n).1 : ℕ) : ℚ) := by
        simp
        exact_mod_cast hn
      have hnonneg : ∀ i : Fin n,
          (0 : ℚ) ≤ (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) := by
        intro i
        positivity
      have hsum_pos :
          (0 : ℚ) < ∑ i : Fin n,
            (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) := by
        exact lt_of_lt_of_le hterm
          (Finset.single_le_sum (fun i hi => hnonneg i)
            (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
      have hsum :
          (∑ i : Fin n,
            (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) * (7 / 10 : ℚ)) =
            (7 / 10 : ℚ) * ∑ i : Fin n,
              (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) := by
        rw [show (∑ i : Fin n,
              (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) * (7 / 10 : ℚ)) =
            ∑ i : Fin n, (7 / 10 : ℚ) *
              (((n - i.1) * Nat.choose n i.1 : ℕ) : ℚ) by
          apply Finset.sum_congr rfl
          intro i hi
          ring]
        rw [Finset.mul_sum]
      rw [hsum]
      nlinarith

end MathlibPlus.Combinatorics.Claim46978
