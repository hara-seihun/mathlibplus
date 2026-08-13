import Mathlib

namespace MathlibPlus.NumberTheory.Claim50200

open Finset

/-- The quotient appearing in the claim. -/
def binomialGcdQuotient (n k : ℕ) : ℕ :=
  n / n.gcd (n.choose k)

/-- The finite set of base-`p` carry positions in `k + (n-k)`. -/
def carryCount (p n k : ℕ) : ℕ :=
  #{i ∈ Ico 1 (Nat.log p n + 1) |
    p ^ i ≤ k % p ^ i + (n - k) % p ^ i}

/-- The source claim's hypothesis that `n` has two distinct prime divisors. -/
def HasTwoDistinctPrimeDivisors (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n

theorem binomialGcdQuotient_dvd_gcd {n k : ℕ}
    (hk0 : k ≠ 0) (hkn : k ≤ n) :
    binomialGcdQuotient n k ∣ n.gcd k := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst hn
    simp at hkn
    exact hk0 hkn
  have hc0 : n.choose k ≠ 0 := Nat.choose_ne_zero hkn
  let d := n.gcd (n.choose k)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn0)
  have hnk : n ∣ n.choose k * k := by
    refine ⟨(n - 1).choose (k - 1), ?_⟩
    have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    simpa [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hk1] using h.symm
  have hdc : d ∣ n.choose k := Nat.gcd_dvd_right _ _
  have hdn : d ∣ n := Nat.gcd_dvd_left _ _
  have hquot' : n / d ∣ (n.choose k * k) / d := by
    apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_left hdc k)).2
    simpa [d, Nat.mul_div_cancel' hdn, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnk
  have hquot : n / d ∣ (n.choose k / d) * k := by
    simpa [Nat.mul_comm, Nat.mul_div_assoc k hdc] using hquot'
  have hcop : (n / d).Coprime (n.choose k / d) :=
    Nat.coprime_div_gcd_div_gcd hdpos
  have hquot_k : n / d ∣ k := hcop.dvd_of_dvd_mul_left hquot
  have hquot_n : n / d ∣ n := Nat.div_dvd_of_dvd hdn
  change n / d ∣ n.gcd k
  exact Nat.dvd_gcd hquot_n hquot_k

theorem factorization_binomialGcdQuotient {p n k : ℕ}
    (hp : p.Prime) (hn0 : n ≠ 0) (hkn : k ≤ n) :
    (binomialGcdQuotient n k).factorization p =
      max 0 (n.factorization p - carryCount p n k) := by
  have hc0 : n.choose k ≠ 0 := Nat.choose_ne_zero hkn
  have hdn : n.gcd (n.choose k) ∣ n := Nat.gcd_dvd_left _ _
  unfold binomialGcdQuotient
  rw [Nat.factorization_div hdn, Nat.factorization_gcd hn0 hc0]
  change n.factorization p - min (n.factorization p) ((n.choose k).factorization p) = _
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  unfold carryCount
  simp only [Nat.succ_eq_add_one]
  omega

/-- The divisibility conclusion with the source claim's displayed domain. -/
theorem claim50200_quotient_dvd_gcd {n k : ℕ}
    (hpr : HasTwoDistinctPrimeDivisors n) (hk : 2 ≤ k) (hkn : k ≤ n / 2) :
    binomialGcdQuotient n k ∣ n.gcd k := by
  rcases hpr with ⟨p, q, hp, hq, hpq, hpn, hqn⟩
  exact binomialGcdQuotient_dvd_gcd (by omega) (by omega)

/-- The valuation formula with the source claim's displayed domain. -/
theorem claim50200_factorization {p n k : ℕ}
    (hpr : HasTwoDistinctPrimeDivisors n) (hk : 2 ≤ k) (hkn : k ≤ n / 2)
    (hp : p.Prime) :
    (binomialGcdQuotient n k).factorization p =
      max 0 (n.factorization p - carryCount p n k) := by
  rcases hpr with ⟨q, r, hq, hr, hqr, hqn, hrn⟩
  exact factorization_binomialGcdQuotient hp (by omega) (by omega)

end MathlibPlus.NumberTheory.Claim50200
