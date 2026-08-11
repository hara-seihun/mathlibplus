import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

namespace MathlibPlus.Algebra.Claim4764

/-- Claim 4764: for the finite Jensen-lattice polynomials
`P_{d,n}(x) = Σ_{j=0}^d choose(d,j) a_(n+j) x^j`, differentiation gives
`P'_{d,n} = d P_{d-1,n+1}` for `d ≥ 1`. -/
theorem jensen_lattice_derivative {R : Type*} [CommRing R]
    (a : ℕ → R) {d n : ℕ} (hd : 1 ≤ d) :
    let P : ℕ → ℕ → Polynomial R := fun d n =>
      Finset.sum (Finset.range (d + 1)) (fun j =>
        Polynomial.monomial j ((Nat.choose d j : R) * a (n + j)))
    (P d n).derivative = (d : R) • P (d - 1) (n + 1) := by
  classical
  dsimp
  rw [Polynomial.derivative_sum]
  simp_rw [Polynomial.derivative_monomial]
  apply Polynomial.ext
  intro k
  simp [Polynomial.coeff_monomial]
  by_cases hk : k ≤ d - 1
  · have hmem : k + 1 ∈ Finset.range (d + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single (k + 1)]
    · simp only [Nat.add_sub_cancel]
      have hchoose : d.choose (k + 1) * (k + 1) = d * (d - 1).choose k := by
        simpa [Nat.sub_add_cancel hd] using
          (Nat.add_one_mul_choose_eq (d - 1) k).symm
      have hindex : n + (k + 1) = n + 1 + k := by omega
      rw [hindex]
      simp only [if_true, if_pos hk]
      calc
        (d.choose (k + 1) : R) * a (n + 1 + k) * ((k + 1 : ℕ) : R) =
            ((d.choose (k + 1) * (k + 1) : ℕ) : R) * a (n + 1 + k) := by
              push_cast
              ring
        _ = ((d * (d - 1).choose k : ℕ) : R) * a (n + 1 + k) := by rw [hchoose]
        _ = (d : R) * ((d - 1).choose k : R) * a (n + 1 + k) := by
          push_cast
          rfl
        _ = (d : R) * (((d - 1).choose k : R) * a (n + 1 + k)) := by ring
    · intro b hb hbk
      by_cases hb0 : b = 0
      · subst b
        simp
      · have hbpos : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
        by_cases hcond : b - 1 = k
        · have : b = k + 1 := by omega
          exact (hbk this).elim
        · simp [hcond]
    · exact (by simp [hmem])
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hb0 : b = 0
    · subst b
      simp
    · have hbpos : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
      by_cases hcond : b - 1 = k
      · have hbval : b = k + 1 := by omega
        have hb_lt : b < d + 1 := by simpa using (Finset.mem_range.mp hb)
        exfalso
        omega
      · simp [hcond]

end MathlibPlus.Algebra.Claim4764
