import Mathlib

namespace MathlibPlus.Algebra.Claim35248

open scoped BigOperators

private theorem root_eq_esymm_one
    {D : Type*} [CommRing D] [IsDomain D] [CharZero D]
    (t : ℕ) (u : Fin t → D)
    (hvanish : ∀ k, 2 ≤ k → k ≤ t →
      (Multiset.map u (Finset.univ : Finset (Fin t)).val).esymm k = 0)
    (a : Fin t) (ha : u a ≠ 0) :
    u a = (Multiset.map u (Finset.univ : Finset (Fin t)).val).esymm 1 := by
  classical
  let s : Multiset D := Multiset.map u (Finset.univ : Finset (Fin t)).val
  have hs_card : s.card = t := by
    simp [s, Finset.card_def]
  have ht : 1 ≤ t := by
    have ha' := a.isLt
    omega
  have hsum_subset :
      ({0, 1} : Finset ℕ) ⊆ Finset.range (t + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp
    · simp only [Finset.mem_range]
      omega
  have hsum_zero : ∀ k ∈ Finset.range (t + 1),
      k ∉ ({0, 1} : Finset ℕ) →
        Polynomial.eval (-u a)
            (Polynomial.C (s.esymm k) * Polynomial.X ^ (t - k)) = 0 := by
    intro k hk hnot
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      omega
    have hkt : k ≤ t := by
      simp only [Finset.mem_range] at hk
      omega
    rw [hvanish k hk2 hkt]
    simp
  have hsum :
      (∑ k ∈ ({0, 1} : Finset ℕ),
          Polynomial.eval (-u a)
            (Polynomial.C (s.esymm k) * Polynomial.X ^ (t - k))) =
      ∑ k ∈ Finset.range (t + 1),
          Polynomial.eval (-u a)
            (Polynomial.C (s.esymm k) * Polynomial.X ^ (t - k)) :=
    Finset.sum_subset hsum_subset hsum_zero
  have hsum_poly :
      (∑ k ∈ ({0, 1} : Finset ℕ),
          Polynomial.C (s.esymm k) * Polynomial.X ^ (t - k)) =
      ∑ k ∈ Finset.range (t + 1),
          Polynomial.C (s.esymm k) * Polynomial.X ^ (t - k) := by
    apply Finset.sum_subset hsum_subset
    intro k hk hnot
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      omega
    have hkt : k ≤ t := by
      simp only [Finset.mem_range] at hk
      omega
    rw [hvanish k hk2 hkt]
    simp
  have hsum_poly_s :
      (∑ k ∈ ({0, 1} : Finset ℕ),
          Polynomial.C (s.esymm k) * Polynomial.X ^ (s.card - k)) =
      ∑ k ∈ Finset.range (s.card + 1),
          Polynomial.C (s.esymm k) * Polynomial.X ^ (s.card - k) := by
    simpa [hs_card] using hsum_poly
  have hpoly :
      (s.map (fun r => Polynomial.X + Polynomial.C r)).prod =
        Polynomial.C (s.esymm 0) * Polynomial.X ^ t +
          Polynomial.C (s.esymm 1) * Polynomial.X ^ (t - 1) := by
    rw [Multiset.prod_X_add_C_eq_sum_esymm]
    rw [← hsum_poly_s]
    rw [Finset.sum_pair (by norm_num)]
    simpa [hs_card]
  have hprod_poly :
      (s.map (fun r => Polynomial.X + Polynomial.C r)).prod =
        ∏ k : Fin t, (Polynomial.X + Polynomial.C (u k)) := by
    simp [s, Finset.prod_eq_multiset_prod, Function.comp_def]
  have hprod :
      Polynomial.eval (-u a)
          (s.map (fun r => Polynomial.X + Polynomial.C r)).prod = 0 := by
    rw [hprod_poly, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  rw [hpoly] at hprod
  have hroot :
      (-u a) ^ t + s.esymm 1 * (-u a) ^ (t - 1) = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Multiset.esymm, hs_card] using hprod
  have hfactor :
      (-u a) ^ t + s.esymm 1 * (-u a) ^ (t - 1) =
        (-1 : D) ^ (t - 1) * (u a ^ (t - 1) * (s.esymm 1 - u a)) := by
    have hpowneg : (-u a) ^ t = (-1 : D) ^ t * (u a) ^ t := neg_pow _ _
    have hpowneg' : (-u a) ^ (t - 1) = (-1 : D) ^ (t - 1) * (u a) ^ (t - 1) :=
      neg_pow _ _
    have ht_eq : t - 1 + 1 = t := Nat.sub_add_cancel ht
    have hpow_one : (-1 : D) ^ t = -(-1 : D) ^ (t - 1) := by
      calc
        (-1 : D) ^ t = (-1 : D) ^ (t - 1 + 1) := by rw [ht_eq]
        _ = (-1 : D) ^ (t - 1) * (-1 : D) := by rw [pow_succ]
        _ = -(-1 : D) ^ (t - 1) := by ring
    have hpow_u : (u a) ^ t = (u a) ^ (t - 1) * u a := by
      calc
        (u a) ^ t = (u a) ^ (t - 1 + 1) := by rw [ht_eq]
        _ = (u a) ^ (t - 1) * u a := by rw [pow_succ]
    rw [hpowneg, hpowneg', hpow_one, hpow_u]
    ring
  rw [hfactor] at hroot
  have hinner : u a ^ (t - 1) * (s.esymm 1 - u a) = 0 :=
    (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (by norm_num))
  have : s.esymm 1 - u a = 0 :=
    (mul_eq_zero.mp hinner).resolve_left (pow_ne_zero _ ha)
  simpa [s] using (sub_eq_zero.mp this).symm


/-- In a characteristic-zero domain, vanishing elementary symmetric functions
of all orders from two through the family size force at most one nonzero entry. -/
theorem allButOneNonzeroOfElementarySymmetricVanishing
    {D : Type*} [CommRing D] [IsDomain D] [CharZero D]
    (t : ℕ) (u : Fin t → D)
    (hvanish : ∀ k, 2 ≤ k → k ≤ t →
      (Multiset.map u (Finset.univ : Finset (Fin t)).val).esymm k = 0) :
    ∀ i j, u i ≠ 0 → u j ≠ 0 → i = j := by
  classical
  let s : Multiset D := Multiset.map u (Finset.univ : Finset (Fin t)).val
  have hroot : ∀ a, u a ≠ 0 → u a = s.esymm 1 := by
    intro a ha
    exact root_eq_esymm_one t u hvanish a ha
  have hsum_one : s.esymm 1 = ∑ k ∈ (Finset.univ : Finset (Fin t)), u k := by
    rw [show s = Multiset.map u (Finset.univ : Finset (Fin t)).val by rfl]
    rw [Finset.esymm_map_val, Finset.powersetCard_one]
    simp
  intro i j hi hj
  by_contra hne
  let nz : Finset (Fin t) := Finset.univ.filter (fun k => u k ≠ 0)
  have hi_nz : i ∈ nz := by simp [nz, hi]
  have hj_nz : j ∈ nz := by simp [nz, hj]
  have hcard_two : 2 ≤ nz.card := by
    by_contra hcard
    have hcard_one : nz.card ≤ 1 := by omega
    have hij : i = j := (Finset.card_le_one.mp hcard_one) i hi_nz j hj_nz
    exact hne hij
  have hsum_eq :
      (∑ k ∈ (Finset.univ : Finset (Fin t)), u k) =
        ∑ k ∈ nz, u k := by
    symm
    apply Finset.sum_subset (by simp [nz])
    intro k hk hknz
    have hkzero : u k = 0 := by
      by_contra hkzero
      exact hknz (by simp [nz, hk, hkzero])
    exact hkzero
  have hsum_nz : (∑ k ∈ nz, u k) = nz.card • s.esymm 1 := by
    apply Finset.sum_eq_card_nsmul
    intro k hk
    have hk' : k ∈ (Finset.univ : Finset (Fin t)) ∧ u k ≠ 0 := by
      simpa [nz] using hk
    exact hroot k hk'.2
  have hcount : s.esymm 1 = nz.card • s.esymm 1 :=
    hsum_one.trans (hsum_eq.trans hsum_nz)
  have hesymm_ne : s.esymm 1 ≠ 0 := by
    intro hz
    have : u i = 0 := by rw [hroot i hi, hz]
    exact hi this
  have hmul : ((nz.card : D) - 1) * s.esymm 1 = 0 := by
    calc
      ((nz.card : D) - 1) * s.esymm 1 =
          (nz.card : D) * s.esymm 1 - s.esymm 1 := by
            ring
      _ = 0 := by
        rw [nsmul_eq_mul] at hcount
        exact sub_eq_zero.mpr hcount.symm
  have hcast : (nz.card : D) = 1 := by
    have hz : (nz.card : D) - 1 = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hesymm_ne
    exact sub_eq_zero.mp hz
  have hcard_one : nz.card = 1 := by
    exact_mod_cast hcast
  omega

end MathlibPlus.Algebra.Claim35248
