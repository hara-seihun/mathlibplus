import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim35918

private lemma sum_mod_div (d r : ℕ) (hr : r < d) :
    ∑ t ∈ Finset.range d, (t + r) / d = r := by
  by_cases hzero : r = 0
  · subst r
    apply Finset.sum_eq_zero
    intro t ht
    exact Nat.div_eq_of_lt (Finset.mem_range.mp ht)
  · have hpos : 0 < r := Nat.pos_of_ne_zero hzero
    have hd : 0 < d := lt_trans hpos hr
    have hsplit : d = (d - r) + r := by omega
    have hrange : Finset.range d = Finset.range ((d - r) + r) := by
      congr 1
    rw [hrange, Finset.sum_range_add]
    have hleft : ∀ t < d - r, (t + r) / d = 0 := by
      intro t ht
      apply Nat.div_eq_of_lt
      omega
    have hright : ∀ x < r, (d - r + x + r) / d = 1 := by
      intro x hx
      have hsum : d - r + x + r = d + x := by omega
      rw [hsum]
      have hxd : x < d := lt_trans hx hr
      rw [show d + x = x + d * 1 by omega, Nat.add_mul_div_left _ _ hd]
      simp [Nat.div_eq_of_lt hxd]
    have hzleft : ∑ t ∈ Finset.range (d - r), (t + r) / d = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      exact hleft t (Finset.mem_range.mp ht)
    have hone : ∑ x ∈ Finset.range r, (d - r + x + r) / d = r := by
      calc
        ∑ x ∈ Finset.range r, (d - r + x + r) / d =
            ∑ x ∈ Finset.range r, 1 := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hright x (Finset.mem_range.mp hx)
        _ = r := by simp
    rw [hzleft, hone]
    simp

private lemma sum_floor_shift (d N : ℕ) (hd : 0 < d) :
    ∑ t ∈ Finset.range d, (t + N) / d = N := by
  let q := N / d
  let r := N % d
  have hr : r < d := Nat.mod_lt _ hd
  have hN : d * q + r = N := by
    dsimp [q, r]
    exact Nat.div_add_mod N d
  have hterm : ∀ t, (t + N) / d = (t + r) / d + q := by
    intro t
    rw [← hN]
    have heq : t + (d * q + r) = (t + r) + d * q := by omega
    rw [heq]
    exact Nat.add_mul_div_left (t + r) q hd
  calc
    ∑ t ∈ Finset.range d, (t + N) / d =
        ∑ t ∈ Finset.range d, ((t + r) / d + q) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hterm t
    _ = (∑ t ∈ Finset.range d, (t + r) / d) +
        ∑ _t ∈ Finset.range d, q := by
          rw [Finset.sum_add_distrib]
    _ = r + d * q := by rw [sum_mod_div d r hr]; simp
    _ = N := by simpa [Nat.add_comm] using hN

private lemma floor_sum_zero (d : ℕ) (hd : 0 < d) :
    ∑ t ∈ Finset.range d, (((t / d : ℕ) : ℚ)) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  exact_mod_cast Nat.div_eq_of_lt (Finset.mem_range.mp ht)

private lemma floor_remainder_sum_zero (d N : ℕ) (hd : 0 < d) :
    ∑ t ∈ Finset.range d,
      (((((t + N) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ)) -
        (N : ℚ) / (d : ℚ)) = 0 := by
  have hsumNat := sum_floor_shift d N hd
  have hsumRat :
      ∑ t ∈ Finset.range d, (((t + N) / d : ℕ) : ℚ) = (N : ℚ) := by
    exact_mod_cast hsumNat
  have hfloor := floor_sum_zero d hd
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumRat, hfloor]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

private lemma floor_remainder_periodic (d N t : ℕ) (hd : 0 < d) :
    (((((t + d + N) / d : ℕ) : ℚ) - (((t + d) / d : ℕ) : ℚ)) -
        (N : ℚ) / (d : ℚ)) =
      (((((t + N) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ)) -
        (N : ℚ) / (d : ℚ)) := by
  have h₁ : (t + d + N) / d = (t + N) / d + 1 := by
    have h : t + d + N = (t + N) + d * 1 := by omega
    rw [h, Nat.add_mul_div_left _ _ hd]
  have h₂ : (t + d) / d = t / d + 1 := by
    have h : t + d = t + d * 1 := by omega
    rw [h, Nat.add_mul_div_left _ _ hd]
  rw [h₁, h₂]
  push_cast
  ring

private lemma sum_periodic_mul (d k : ℕ) (f : ℕ → ℚ)
    (hper : ∀ t, f (t + d) = f t) :
    (∑ t ∈ Finset.range (d * k), f t) =
      k * (∑ t ∈ Finset.range d, f t) := by
  have hshift : ∀ (j x : ℕ), f (d * j + x) = f x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        calc
          f (d * (j + 1) + x) = f (d * j + x + d) := by
            congr 1
            simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = f (d * j + x) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hper (d * j + x)
          _ = f x := ih x
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hs :
          (∑ x ∈ Finset.range d, f (d * k + x)) =
            ∑ x ∈ Finset.range d, f x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hshift k x
      rw [hs]
      push_cast
      ring

/-- The centered interval floor remainder has zero mean over every positive
integer period divisible by its modulus.  The source's real-shift notation
is represented here by integer shifts, and its covariance bound remains an
explicit fidelity boundary. -/
theorem floorRemainder_mean_zero_claim35918
    (d N L : ℕ) (hd : 0 < d) (hL : d ∣ L) :
    (∑ t ∈ Finset.range L,
      (((((t + N) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ)) -
        (N : ℚ) / (d : ℚ))) / (L : ℚ) = 0 := by
  obtain ⟨k, rfl⟩ := hL
  let f : ℕ → ℚ := fun t =>
    (((((t + N) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ)) -
      (N : ℚ) / (d : ℚ))
  have hper : ∀ t, f (t + d) = f t := by
    intro t
    dsimp [f]
    exact floor_remainder_periodic d N t hd
  have hsum : (∑ t ∈ Finset.range (d * k), f t) = 0 := by
    rw [sum_periodic_mul d k f hper, floor_remainder_sum_zero d N hd]
    simp
  have hzero :
      (∑ t ∈ Finset.range (d * k),
        (((((t + N) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ)) -
          (N : ℚ) / (d : ℚ))) = 0 := by
    simpa [f] using hsum
  rw [hzero]
  simp

end MathlibPlus.NumberTheory.Claim35918
