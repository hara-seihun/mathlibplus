import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory

/-- The unique smooth/rough factorization of claim 14089.  A finite set of
primes is represented by a `Finset ℕ` together with a proof that each member
is prime.  The canonical smooth factor is obtained by filtering the prime
factorization of `n`; the theorem does not introduce an arbitrary ordering of
`P`. -/
theorem uniqueSmoothRoughFactorization_claim14089
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) (hn : 0 < n) :
    ∃ a r : ℕ,
      n = a * r ∧
      (∀ p, Nat.Prime p → p ∣ a → p ∈ P) ∧
      r.Coprime (∏ p ∈ P, p) ∧
      (∀ a' r' : ℕ,
        n = a' * r' →
        (∀ p, Nat.Prime p → p ∣ a' → p ∈ P) →
        r'.Coprime (∏ p ∈ P, p) →
        a' = a ∧ r' = r) := by
  classical
  let f : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∈ P)
  have hf_le : f ≤ n.factorization := by
    rw [Finsupp.le_def]
    intro p
    simp only [f, Finsupp.filter_apply]
    split_ifs with hp
    · exact le_rfl
    · exact Nat.zero_le _
  have hf_prime : ∀ p ∈ f.support, Nat.Prime p := by
    intro p hp
    have hp' : p ∈ n.factorization.support := by
      rw [Finsupp.support_filter] at hp
      exact (Finset.mem_filter.1 hp).1
    simpa [Nat.support_factorization] using Nat.prime_of_mem_primeFactors hp'
  let a : ℕ := f.prod (fun p k => p ^ k)
  have ha_factor : a.factorization = f := by
    exact Nat.factorization_prod_pow_eq_self_of_le_factorization hf_le
  have ha_dvd : a ∣ n := by
    exact Nat.prod_pow_dvd_of_le_factorization hf_le
  have ha_ne : a ≠ 0 := by
    rw [Finsupp.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (hf_prime p hp).ne_zero
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha_ne
  obtain ⟨r, hr⟩ := ha_dvd
  have hr_ne : r ≠ 0 := by
    intro hr0
    subst hr0
    simp at hr
    exact (Nat.ne_of_gt hn) hr
  have hfac : n.factorization = a.factorization + r.factorization := by
    rw [hr, Nat.factorization_mul ha_ne hr_ne]
  have hr_factor_zero : ∀ p ∈ P, r.factorization p = 0 := by
    intro p hpP
    have hpr : f p = n.factorization p := by
      simp [f, Finsupp.filter_apply, hpP]
    have hpoint := congrArg (fun g : ℕ →₀ ℕ => g p) hfac
    change n.factorization p = a.factorization p + r.factorization p at hpoint
    rw [ha_factor] at hpoint
    rw [hpr] at hpoint
    omega
  have hr_not_dvd : ∀ p ∈ P, ¬p ∣ r := by
    intro p hpP hpr
    have hpos : 0 < r.factorization p :=
      (hP p hpP).factorization_pos_of_dvd hr_ne hpr
    exact (Nat.ne_of_gt hpos) (hr_factor_zero p hpP)
  have hrough : r.Coprime (∏ p ∈ P, p) := by
    rw [Nat.coprime_prod_right_iff]
    intro p hpP
    exact (hP p hpP).coprime_iff_not_dvd.mpr (hr_not_dvd p hpP) |>.symm
  have hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ∈ P := by
    intro p hp hpa
    have hpos : 0 < a.factorization p := hp.factorization_pos_of_dvd ha_ne hpa
    have hfpos : f p ≠ 0 := by
      rw [← ha_factor]
      exact hpos.ne'
    by_contra hpP
    have hfzero : f p = 0 := by
      simp [f, Finsupp.filter_apply, hpP]
    exact (Nat.ne_of_gt hpos) (by simpa [ha_factor] using hfzero)
  refine ⟨a, r, hr, hsmooth, hrough, ?_⟩
  intro a' r' hr' hsmooth' hrough'
  have ha'_ne : a' ≠ 0 := by
    intro ha'0
    subst ha'0
    simp at hr'
    exact (Nat.ne_of_gt hn) hr'
  have hr'_ne : r' ≠ 0 := by
    intro hr'0
    subst hr'0
    simp at hr'
    exact (Nat.ne_of_gt hn) hr'
  have hfac' : n.factorization = a'.factorization + r'.factorization := by
    rw [hr', Nat.factorization_mul ha'_ne hr'_ne]
  have hf_eq_a'_factor : ∀ p, f p = a'.factorization p := by
    intro p
    by_cases hpP : p ∈ P
    · have hprcop : r'.Coprime p := by
        have h := (Nat.coprime_prod_right_iff.mp hrough') p hpP
        exact h
      have hnot : ¬p ∣ r' := (hP p hpP).coprime_iff_not_dvd.mp hprcop.symm
      have hrzero : r'.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hnot
      have hpoint := congrArg (fun g : ℕ →₀ ℕ => g p) hfac'
      change n.factorization p = a'.factorization p + r'.factorization p at hpoint
      rw [hrzero] at hpoint
      have hfn : f p = n.factorization p := by
        simp [f, Finsupp.filter_apply, hpP]
      rw [hfn]
      omega
    · have hfzero : f p = 0 := by
        simp [f, Finsupp.filter_apply, hpP]
      by_cases hpPrime : Nat.Prime p
      · have hnot : ¬p ∣ a' := by
          intro hpa'
          exact hpP (hsmooth' p hpPrime hpa')
        rw [hfzero, Nat.factorization_eq_zero_of_not_dvd hnot]
      · rw [hfzero, Nat.factorization_eq_zero_of_not_prime _ hpPrime]
  have ha_eq : a' = a := by
    apply Nat.eq_of_factorization_eq ha'_ne ha_ne
    intro p
    rw [ha_factor]
    exact (hf_eq_a'_factor p).symm
  have hr_eq : r' = r := by
    apply Nat.mul_left_cancel ha_pos
    calc
      a * r' = a' * r' := by rw [ha_eq]
      _ = n := hr'.symm
      _ = a * r := hr
  exact ⟨ha_eq, hr_eq⟩

end MathlibPlus.NumberTheory
