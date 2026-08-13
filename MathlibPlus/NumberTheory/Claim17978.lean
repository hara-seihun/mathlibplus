import MathlibPlus.NumberTheory.DivisorCoordinateReflection

namespace MathlibPlus.NumberTheory.Claim17978

/-- A finite involution whose values occur with opposite signs has zero sum. -/
theorem sum_eq_zero_of_involutive_neg
    (s : Finset ℕ) (ι : ℕ → ℕ) (f : ℕ → ℝ)
    (hmem : ∀ x ∈ s, ι x ∈ s)
    (hinv : ∀ x ∈ s, ι (ι x) = x)
    (hneg : ∀ x ∈ s, f (ι x) = -f x) :
    ∑ x ∈ s, f x = 0 := by
  have hsum : (∑ x ∈ s, f (ι x)) = ∑ x ∈ s, f x := by
    apply Finset.sum_bij (fun x _ => ι x)
    · intro x hx
      exact hmem x hx
    · intro x₁ hx₁ x₂ hx₂ h
      have h' := congrArg ι h
      simpa [hinv x₁ hx₁, hinv x₂ hx₂] using h'
    · intro y hy
      refine ⟨ι y, hmem y hy, ?_⟩
      exact hinv y hy
    · intro x hx
      rfl
  have hneg_sum : (∑ x ∈ s, f (ι x)) = -∑ x ∈ s, f x := by
    calc
      (∑ x ∈ s, f (ι x)) = ∑ x ∈ s, -f x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hneg x hx
      _ = -∑ x ∈ s, f x := Finset.sum_neg_distrib f
  have hsum_neg : (∑ x ∈ s, f x) = -∑ x ∈ s, f x :=
    hsum.symm.trans hneg_sum
  linarith

/-- The complementary-divisor map is an involution on the positive divisors. -/
theorem complementaryDivisor_involutive
    (k : ℕ) (hk : 0 < k) :
    ∀ m ∈ k.divisors, k / (k / m) = m := by
  intro m hm
  have hdiv : m ∣ k := Nat.dvd_of_mem_divisors hm
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hdiv hk
  have hqpos : 0 < k / m := Nat.div_pos (Nat.le_of_dvd hk hdiv) hmpos
  have hqdiv : k / m ∣ k := by
    refine ⟨m, ?_⟩
    exact (Nat.div_mul_cancel hdiv).symm.trans (by rw [Nat.mul_comm])
  have h1 : (k / m) * m = k := Nat.div_mul_cancel hdiv
  have h2 : (k / (k / m)) * (k / m) = k := Nat.div_mul_cancel hqdiv
  apply Nat.eq_of_mul_eq_mul_right hqpos
  calc
    (k / (k / m)) * (k / m) = k := h2
    _ = m * (k / m) := by simpa [Nat.mul_comm] using h1.symm

/-- Odd relative jets cancel over a complete divisor fibre. -/
theorem divisorFiberSum_eq_zero
    (k : ℕ) (hk : 0 < k) (f : ℕ → ℝ)
    (hneg : ∀ m ∈ k.divisors, f (k / m) = -f m) :
    ∑ m ∈ k.divisors, f m = 0 := by
  apply sum_eq_zero_of_involutive_neg k.divisors (fun m => k / m) f
  · exact fun m hm => by
      rw [Nat.mem_divisors]
      refine ⟨?_, Nat.ne_of_gt hk⟩
      refine ⟨m, ?_⟩
      exact (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)).symm
  · exact complementaryDivisor_involutive k hk
  · exact hneg

end MathlibPlus.NumberTheory.Claim17978
