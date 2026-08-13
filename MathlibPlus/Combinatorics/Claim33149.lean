import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

open scoped BigOperators

/-- Every zero-sum function on the prime cyclic field is a cyclic finite difference. -/
theorem cyclicFiniteDifference_surjectiveOnZeroSum_claim33149
    (p : ℕ) (hp : p.Prime) (f : ZMod p → ZMod p)
    (hf : ∑ i ∈ Finset.range p, f (i : ZMod p) = 0) :
    ∃ n : ZMod p → ZMod p, ∀ s, n (s + 1) - n s = f s := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
  letI : Fact (1 < p) := ⟨lt_of_lt_of_le Nat.one_lt_two hp.two_le⟩
  let g : ℕ → ZMod p := fun i => f (i : ZMod p)
  let n : ZMod p → ZMod p := fun s => (∑ i ∈ Finset.range s.val, g i)
  have hf' : (∑ i ∈ Finset.range p, g i) = 0 := by
    simpa [g] using hf
  refine ⟨n, ?_⟩
  intro s
  by_cases hs : s.val + 1 < p
  · have hval : (s + 1).val = s.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one]
      exact Nat.mod_eq_of_lt (by simpa using hs)
    have hgs : g s.val = f s := by
      simp only [g, ZMod.natCast_zmod_val]
    simp only [n, hval, Finset.sum_range_succ]
    rw [hgs]
    abel
  · have hslt : s.val < p := ZMod.val_lt s
    have hlast : s.val + 1 = p := by omega
    have hsval : s.val = p - 1 := by omega
    have hzero : (s + 1).val = 0 := by
      rw [ZMod.val_add, ZMod.val_one, hlast, Nat.mod_self]
    have hsum : (∑ i ∈ Finset.range (p - 1), g i) + g (p - 1) = 0 := by
      calc
        (∑ i ∈ Finset.range (p - 1), g i) + g (p - 1) =
            ∑ i ∈ Finset.range ((p - 1) + 1), g i :=
          (Finset.sum_range_succ g (p - 1)).symm
        _ = ∑ i ∈ Finset.range p, g i := by
          have h : (p - 1) + 1 = p := by omega
          rw [h]
        _ = 0 := hf'
    have hgs : g (p - 1) = f s := by
      simp only [g, Nat.mod_eq_of_lt (show p - 1 < p by omega)]
      have hps : ((p - 1 : ℕ) : ZMod p) = s := by
        rw [← hsval, ZMod.natCast_zmod_val]
      exact congrArg f hps
    simp only [n, hzero, Finset.sum_range_zero, zero_sub, hsval]
    calc
      -∑ i ∈ Finset.range (p - 1), g i = g (p - 1) :=
        neg_eq_of_add_eq_zero_right hsum
      _ = f s := hgs

/-- Every cyclic finite difference has zero total sum. -/
theorem cyclicFiniteDifference_sum_zero_claim33149
    (p : ℕ) (hp : p.Prime) (n : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range p, (n ((i : ZMod p) + 1) - n (i : ZMod p)) = 0 := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
  letI : Fact (1 < p) := ⟨lt_of_lt_of_le Nat.one_lt_two hp.two_le⟩
  let g : ℕ → ZMod p := fun i => n (i : ZMod p)
  have hp2 : 2 ≤ p := hp.two_le
  have hp_eq : (p - 1) + 1 = p := by omega
  have hinner : ∀ i < p - 1,
      n ((i : ZMod p) + 1) - n (i : ZMod p) = g (i + 1) - g i := by
    intro i hi
    simp [g]
  have hlast :
      n (((p - 1 : ℕ) : ZMod p) + 1) - n ((p - 1 : ℕ) : ZMod p) =
        g 0 - g (p - 1) := by
    have hz : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
      calc
        ((p - 1 : ℕ) : ZMod p) + 1 =
            ((p - 1 + 1 : ℕ) : ZMod p) := by norm_num
        _ = (p : ZMod p) := by rw [hp_eq]
        _ = 0 := ZMod.natCast_self p
    simp [g, hz]
  calc
    ∑ i ∈ Finset.range p, (n ((i : ZMod p) + 1) - n (i : ZMod p)) =
        (∑ i ∈ Finset.range (p - 1),
          (n ((i : ZMod p) + 1) - n (i : ZMod p))) +
          (n (((p - 1 : ℕ) : ZMod p) + 1) - n ((p - 1 : ℕ) : ZMod p)) := by
            simpa only [hp_eq] using
              (Finset.sum_range_succ
                (fun i => n ((i : ZMod p) + 1) - n (i : ZMod p)) (p - 1))
    _ = (∑ i ∈ Finset.range (p - 1), (g (i + 1) - g i)) +
          (g 0 - g (p - 1)) := by
            rw [hlast]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            apply hinner i
            exact Finset.mem_range.mp hi
    _ = (g (p - 1) - g 0) + (g 0 - g (p - 1)) := by
          rw [Finset.sum_range_sub]
    _ = 0 := by abel

/-- The image of the cyclic finite-difference map is exactly the zero-sum
subspace. -/
theorem cyclicDifference_image_iff_zeroSum_claim33149
    (p : ℕ) (hp : p.Prime) (f : ZMod p → ZMod p) :
    (∃ n : ZMod p → ZMod p, ∀ s, n (s + 1) - n s = f s) ↔
      ∑ i ∈ Finset.range p, f (i : ZMod p) = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    calc
      ∑ i ∈ Finset.range p, f (i : ZMod p) =
          ∑ i ∈ Finset.range p,
            (n ((i : ZMod p) + 1) - n (i : ZMod p)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hn]
      _ = 0 := cyclicFiniteDifference_sum_zero_claim33149 p hp n
  · intro hf
    exact cyclicFiniteDifference_surjectiveOnZeroSum_claim33149 p hp f hf

/-- The kernel of the cyclic finite-difference map consists of constants. -/
theorem cyclicFiniteDifference_kernel_constants_claim33149
    (p : ℕ) (hp : p.Prime) :
    ∀ n : ZMod p → ZMod p,
      (∀ s, n (s + 1) - n s = 0) ↔ ∃ c, ∀ s, n s = c := by
  intro n
  letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
  letI : Fact (1 < p) := ⟨lt_of_lt_of_le Nat.one_lt_two hp.two_le⟩
  constructor
  · intro hdiff
    let g : ℕ → ZMod p := fun i => n (i : ZMod p)
    have hstep : ∀ i, i + 1 < p → g (i + 1) - g i = 0 := by
      intro i hi
      simpa [g] using hdiff (i : ZMod p)
    have hconst : ∀ s : ZMod p, g s.val = g 0 := by
      intro s
      have hslt : s.val < p := ZMod.val_lt s
      have hsum : (∑ i ∈ Finset.range s.val, (g (i + 1) - g i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply hstep
        have hi' : i < s.val := Finset.mem_range.mp hi
        omega
      have htel : (∑ i ∈ Finset.range s.val, (g (i + 1) - g i)) =
          g s.val - g 0 := Finset.sum_range_sub g s.val
      have hz : g s.val - g 0 = 0 := by
        rw [← htel]
        exact hsum
      exact sub_eq_zero.mp hz
    refine ⟨n 0, ?_⟩
    intro s
    have hs : g s.val = n s := by simp [g, ZMod.natCast_zmod_val]
    have h0 : g 0 = n 0 := by simp [g]
    rw [← hs, ← h0]
    exact hconst s
  · rintro ⟨c, hc⟩ s
    rw [hc (s + 1), hc s]
    exact sub_self c

end MathlibPlus.Combinatorics
