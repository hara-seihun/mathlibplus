import Mathlib

namespace MathlibPlus.NumberTheory.Claim46847

private lemma add_one_mod_ne_self {q a : ℕ} (hq : 2 ≤ q) :
    (a + 1) % q ≠ a % q := by
  intro h
  have ha : a % q < q := Nat.mod_lt _ (by omega)
  have hqpos : 0 < q := by omega
  have hmod : (a + 1) % q = (a % q + 1) % q := by
    rw [Nat.add_mod]
    simp [hqpos]
  rw [hmod] at h
  have hcases : a % q + 1 < q ∨ a % q + 1 = q := by omega
  rcases hcases with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · rw [heq, Nat.mod_self] at h
    omega

/--
A finite set of pairwise distinct prime moduli admits a positive CRT
representative avoiding one prescribed residue at every modulus.  The same
avoidance holds on the entire nonnegative progression by the product of the
moduli (and hence on any bounded interval cut from that progression).
-/
theorem crt_avoidance (A : Finset ℕ)
    (hp : ∀ q ∈ A, q.Prime) (a : ℕ → ℕ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ n₀ ≤ ∏ q ∈ A, q ∧
      ∀ q ∈ A, ∀ j : ℕ, (n₀ + j * (∏ q ∈ A, q)) % q ≠ a q % q := by
  let s : ℕ → ℕ := fun q => q
  let b : ℕ → ℕ := fun q => (a q + 1) % q
  have hs : ∀ q ∈ A, s q ≠ 0 := by
    intro q hq
    exact (hp q hq).ne_zero
  have hcop : Set.Pairwise A (fun p q => Nat.Coprime (s p) (s q)) := by
    intro p hpA q hqA hpq
    exact (Nat.coprime_primes (hp p hpA) (hp q hqA)).2 hpq
  let r : ℕ := Nat.chineseRemainderOfFinset b s A hs hcop
  have hrlt : r < ∏ q ∈ A, q := by
    exact Nat.chineseRemainderOfFinset_lt_prod b s hs hcop
  let n₀ : ℕ := if r = 0 then ∏ q ∈ A, q else r
  refine ⟨n₀, ?_, ?_, ?_⟩
  · by_cases hr : r = 0
    · simp [n₀, hr]
      have hpos : 0 < ∏ q ∈ A, q := Finset.prod_pos fun q hq => (hp q hq).pos
      omega
    · simp [n₀, hr]
      omega
  · by_cases hr : r = 0
    · simp [n₀, hr]
    · simp [n₀, hr]
      exact Nat.le_of_lt hrlt
  · intro q hq j
    have hq2 : 2 ≤ q := (hp q hq).two_le
    have hrem : r % q = b q := by
      have hmod := (Nat.chineseRemainderOfFinset b s A hs hcop).property q hq
      simpa [s, b, Nat.ModEq] using hmod
    have hqprod : q ∣ ∏ q ∈ A, q := by
      exact Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hq
    have hnrem : n₀ % q = b q := by
      by_cases hr : r = 0
      · have hb : b q = 0 := by simpa [hr] using hrem.symm
        calc
          n₀ % q = (∏ q ∈ A, q) % q := by simp [n₀, hr]
          _ = 0 := Nat.mod_eq_zero_of_dvd hqprod
          _ = b q := hb.symm
      · simpa [n₀, hr] using hrem
    have hbase : n₀ % q ≠ a q % q := by
      simpa [hnrem, b] using add_one_mod_ne_self (q := q) (a := a q) hq2
    intro hbad
    apply hbase
    have hzero : (∏ q ∈ A, q) ≡ 0 [MOD q] := hqprod.modEq_zero_nat
    have hmul : j * (∏ q ∈ A, q) ≡ j * 0 [MOD q] := hzero.mul_left j
    have hadd := Nat.ModEq.add (Nat.ModEq.rfl : n₀ ≡ n₀ [MOD q]) hmul
    have hshift : (n₀ + j * (∏ q ∈ A, q)) % q = n₀ % q := by
      simpa [Nat.ModEq] using hadd
    rw [hshift] at hbad
    exact hbad

end MathlibPlus.NumberTheory.Claim46847
