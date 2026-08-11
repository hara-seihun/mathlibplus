import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim27627

/-- Claim 27627: the zero-endpoint second-difference recurrence has the
explicit alternating-linear solution, and the second zero endpoint forces
that solution to vanish. -/
theorem zeroEndpointSecondDifference
    {K : Type*} [Field K] [CharZero K]
    (w : ℕ) (v : ℕ → K)
    (hv0 : v 0 = 0) (hvw : v w = 0)
    (hrec : ∀ r : ℕ, 2 ≤ r → r ≤ w →
      v (r - 2) + 2 * v (r - 1) + v r = 0) :
    (∀ p : ℕ, p ≤ w →
      v p = (-1 : K) ^ (p - 1) * (p : K) * v 1) ∧
      (∀ p : ℕ, p ≤ w → v p = 0) := by
  have hformula : ∀ p : ℕ, p ≤ w →
      v p = (-1 : K) ^ (p + 1) * (p : K) * v 1 := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
        intro hp
        cases p with
        | zero =>
            simp [hv0]
        | succ p =>
            cases p with
            | zero =>
                simp
            | succ n =>
                have hr := hrec (n + 2) (by omega) hp
                have hr' : v n + 2 * v (n + 1) + v (n + 2) = 0 := by
                  simpa using hr
                have hn := ih n (by omega) (by omega)
                have hnp := ih (n + 1) (by omega) (by omega)
                have hpow1 : (-1 : K) ^ (n + 2) =
                    -(-1 : K) ^ (n + 1) := by
                  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
                  ring
                have hpow2 : (-1 : K) ^ (n + 3) =
                    (-1 : K) ^ (n + 1) := by
                  calc
                    (-1 : K) ^ (n + 3) =
                        (-1 : K) ^ (n + 2) * (-1 : K) := by
                          rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
                    _ = (-(-1 : K) ^ (n + 1)) * (-1 : K) := by
                          rw [hpow1]
                    _ = (-1 : K) ^ (n + 1) := by ring
                have hpow2' : (-1 : K) ^ ((n + 1 + 1) + 1) =
                    (-1 : K) ^ (n + 1) := by
                  convert hpow2 using 1
                have hnp' : v (n + 1) =
                    (-1 : K) ^ (n + 2) * (n + 1 : K) * v 1 := by
                  simpa [show n + 1 + 1 = n + 2 by omega] using hnp
                calc
                  v (n + 2) = -v n - 2 * v (n + 1) := by
                    linear_combination hr'
                  _ = -((-1 : K) ^ (n + 1) * (n : K) * v 1) -
                        2 * ((-1 : K) ^ (n + 2) * (n + 1 : K) * v 1) := by
                    rw [hn, hnp']
                  _ = (-1 : K) ^ ((n + 1 + 1) + 1) *
                        ((n + 1 + 1 : ℕ) : K) * v 1 := by
                    rw [hpow1, hpow2']
                    norm_num [Nat.cast_add]
                    ring
  have hdisplay : ∀ p : ℕ, p ≤ w →
      v p = (-1 : K) ^ (p - 1) * (p : K) * v 1 := by
    intro p hp
    by_cases hp0 : p = 0
    · subst p
      simp [hv0]
    · have hp1 : 1 ≤ p := by omega
      have hpow : (-1 : K) ^ (p + 1) =
          (-1 : K) ^ (p - 1) := by
        rw [show p + 1 = (p - 1) + 2 by omega, pow_add]
        norm_num
      calc
        v p = (-1 : K) ^ (p + 1) * (p : K) * v 1 := hformula p hp
        _ = (-1 : K) ^ (p - 1) * (p : K) * v 1 := by rw [hpow]
  have hall : ∀ p : ℕ, p ≤ w → v p = 0 := by
    by_cases hw0 : w = 0
    · intro p hp
      have hp0 : p = 0 := by omega
      simpa [hp0] using hv0
    · have hwcast : (w : K) ≠ 0 := by
        exact_mod_cast hw0
      have hcoeff : (-1 : K) ^ (w + 1) * (w : K) ≠ 0 := by
        exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hwcast
      have hwformula := hformula w (le_refl w)
      rw [hvw] at hwformula
      have hv1 : v 1 = 0 := by
        have hz : ((-1 : K) ^ (w + 1) * (w : K)) * v 1 = 0 := by
          simpa using hwformula.symm
        exact (mul_eq_zero.mp hz).resolve_left hcoeff
      intro p hp
      rw [hformula p hp, hv1, mul_zero]
  exact ⟨hdisplay, hall⟩

end MathlibPlus.Algebra.Claim27627
