import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim47027

open Polynomial

/-- The two displayed polynomials have the reported quotient and remainder. -/
theorem division_identity :
    let f : ℚ[X] :=
      C (42756734976 : ℚ) * X ^ 3 + C (1079607558144 : ℚ) * X ^ 2 +
        C (7125388492800 : ℚ) * X + C (9872107634688 : ℚ)
    let g : ℚ[X] := C (1024 : ℚ) * X ^ 2 + C (9984 : ℚ) * X + C (17600 : ℚ)
    let q : ℚ[X] := C (41754624 : ℚ) * X + C (647196672 : ℚ)
    let r : ℚ[X] := C (-71104462848 : ℚ) * X + C (-1518553792512 : ℚ)
    f = q * g + r := by
  dsimp
  norm_num [C_ofNat]
  ring

/-- The nonzero remainder prevents the inner polynomial from dividing the outer. -/
theorem not_dvd :
    let f : ℚ[X] :=
      C (42756734976 : ℚ) * X ^ 3 + C (1079607558144 : ℚ) * X ^ 2 +
        C (7125388492800 : ℚ) * X + C (9872107634688 : ℚ)
    let g : ℚ[X] := C (1024 : ℚ) * X ^ 2 + C (9984 : ℚ) * X + C (17600 : ℚ)
    ¬ g ∣ f := by
  dsimp
  let g : ℚ[X] := C (1024 : ℚ) * X ^ 2 + C (9984 : ℚ) * X + C (17600 : ℚ)
  let r : ℚ[X] := C (-71104462848 : ℚ) * X + C (-1518553792512 : ℚ)
  let q : ℚ[X] := C (41754624 : ℚ) * X + C (647196672 : ℚ)
  let f : ℚ[X] :=
    C (42756734976 : ℚ) * X ^ 3 + C (1079607558144 : ℚ) * X ^ 2 +
      C (7125388492800 : ℚ) * X + C (9872107634688 : ℚ)
  have hid : f = q * g + r := by
    dsimp [f, q, g, r]
    norm_num [C_ofNat]
    ring
  have hg_le : g.degree ≤ (↑(2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    have hm' : 3 ≤ m := by exact_mod_cast hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    have hm1' : 1 ≠ m := by omega
    have hm2 : m ≠ 2 := by omega
    simp [g, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, hm0, hm1, hm1', hm2]
  have hg_ge : (↑(2 : ℕ) : WithBot ℕ) ≤ g.degree := by
    apply Polynomial.le_degree_of_ne_zero
    simp [g, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hr_lt : r.degree < (↑(2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    have hm' : 2 ≤ m := by exact_mod_cast hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    have hm1' : 1 ≠ m := by omega
    simp [r, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, hm0, hm1, hm1']
  have hr_ne : r ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : ℚ[X] => p.coeff 1) hzero
    norm_num [r, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C] at hcoeff
  have hgr : r.degree < g.degree := hr_lt.trans_le hg_ge
  have hgnot : ¬ g ∣ r := Polynomial.not_dvd_of_degree_lt hr_ne hgr
  intro hdiv
  have hqg : g ∣ q * g := by
    refine ⟨q, ?_⟩
    ring
  have hsub : g ∣ f - q * g := dvd_sub hdiv hqg
  have hfr : f - q * g = r := by rw [hid]; ring
  rw [hfr] at hsub
  exact hgnot hsub

end MathlibPlus.Algebra.Claim47027
