import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

private lemma finset_prod_totalDegree_eq {ι σ : Type*}
    (s : Finset ι) (f : ι → MvPolynomial σ ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      rw [MvPolynomial.totalDegree_mul_of_isDomain]
      · rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
      · exact hf i (by simp)
      · exact Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (by simp [hj]))

private lemma factor_totalDegree {ι : Type*} [DecidableEq ι]
    (i : ι) (j : ℕ) :
    (MvPolynomial.X i - MvPolynomial.C (j : ℚ)).totalDegree = 1 := by
  have hlt : (-MvPolynomial.C (j : ℚ) : MvPolynomial ι ℚ).totalDegree <
      (MvPolynomial.X i : MvPolynomial ι ℚ).totalDegree := by
    rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_X]
    norm_num
  rw [sub_eq_add_neg,
    MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt]
  simp

private lemma factor_nonzero {ι : Type*} [DecidableEq ι]
    (i : ι) (j : ℕ) :
    (MvPolynomial.X i - MvPolynomial.C (j : ℚ) : MvPolynomial ι ℚ) ≠ 0 := by
  intro h
  have hdeg := congrArg MvPolynomial.totalDegree h
  rw [factor_totalDegree] at hdeg
  simp at hdeg

private lemma falling_eval (x d : ℕ) :
    (∏ j ∈ Finset.range d, ((x : ℚ) - (j : ℚ))) =
      (d.factorial : ℚ) * (x.choose d : ℚ) := by
  by_cases hxd : d ≤ x
  · calc
      (∏ j ∈ Finset.range d, ((x : ℚ) - (j : ℚ))) =
          (∏ j ∈ Finset.range d, ((x - j : ℕ) : ℚ)) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hjd : j < d := Finset.mem_range.mp hj
            have hjx : j ≤ x := le_trans (Nat.le_of_lt hjd) hxd
            rw [Nat.cast_sub hjx]
      _ = (x.descFactorial d : ℚ) := by
            rw [Nat.descFactorial_eq_prod_range]
            simp only [Nat.cast_prod]
      _ = ((d.factorial * x.choose d : ℕ) : ℚ) := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ = (d.factorial : ℚ) * (x.choose d : ℚ) := by norm_num
  · have hx : x < d := Nat.lt_of_not_ge hxd
    have hzero : (∏ j ∈ Finset.range d, ((x : ℚ) - (j : ℚ))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hx)
      simp
    rw [hzero, Nat.choose_eq_zero_of_lt hx]
    simp

private lemma indicator_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (d x : ι → ℕ)
    (hd : ∑ i, d i = n) (hx : ∑ i, x i = n) :
    (∏ i, (x i).choose (d i)) = if x = d then 1 else 0 := by
  by_cases hxd : x = d
  · subst x
    simp
  · have hex : ∃ i, x i < d i := by
      by_contra hno
      have hno' : ∀ i : ι, ¬ x i < d i := by
        intro i hi
        exact hno ⟨i, hi⟩
      have hle : ∀ i : ι, d i ≤ x i := by
        intro i
        exact Nat.le_of_not_gt (hno' i)
      have hsum :
          (∑ i, (x i - d i)) + ∑ i, d i = ∑ i, x i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.sub_add_cancel (hle i)
      have hzero : (∑ i, (x i - d i)) = 0 := by
        omega
      have hall : ∀ i : ι, x i - d i = 0 := by
        have h' := (Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset ι))
          (f := fun i => x i - d i)
          (fun i hi => Nat.zero_le _)).mp hzero
        exact fun i => h' i (Finset.mem_univ i)
      have hxle : ∀ i : ι, x i ≤ d i := by
        intro i
        exact Nat.le_of_sub_eq_zero (hall i)
      exact hxd (funext fun i => Nat.le_antisymm (hxle i) (hle i))
    obtain ⟨i, hi⟩ := hex
    have hzero : (x i).choose (d i) = 0 := Nat.choose_eq_zero_of_lt hi
    have hprod : (∏ i, (x i).choose (d i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [hxd, hprod]

/-- Claim 20952: the deck-fibre indicator is a degree-`n` binomial
    polynomial, and its values on fixed-mass nonnegative vectors are the
    Kronecker indicator of the deck vector `d`. -/
theorem claim20952_deckFibreIndicator_polynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (d : ι → ℕ) (hd : ∑ i, d i = n) :
    ∃ P : MvPolynomial ι ℚ,
      P.totalDegree = n ∧
      (∀ x : ι → ℕ,
        MvPolynomial.eval₂ (RingHom.id ℚ) (fun i => (x i : ℚ)) P =
          ∏ i, (x i).choose (d i)) ∧
      (∀ x : ι → ℕ, ∑ i, x i = n →
        MvPolynomial.eval₂ (RingHom.id ℚ) (fun i => (x i : ℚ)) P =
          if x = d then 1 else 0) := by
  let scale : ℚ := (∏ i, ((Nat.factorial (d i) : ℕ) : ℚ))⁻¹
  let Q : MvPolynomial ι ℚ :=
    ∏ i, ∏ j ∈ Finset.range (d i),
      (MvPolynomial.X i - MvPolynomial.C (j : ℚ))
  let P : MvPolynomial ι ℚ := scale • Q
  have hinner : ∀ i : ι,
      (∏ j ∈ Finset.range (d i),
        (MvPolynomial.X i - MvPolynomial.C (j : ℚ))).totalDegree = d i := by
    intro i
    rw [finset_prod_totalDegree_eq]
    · simp_rw [factor_totalDegree]
      simp
    · intro j hj
      exact factor_nonzero i j
  have hQ : Q.totalDegree = ∑ i, d i := by
    dsimp [Q]
    rw [finset_prod_totalDegree_eq]
    · exact Finset.sum_congr rfl (fun i hi => hinner i)
    · intro i hi
      exact Finset.prod_ne_zero_iff.mpr (fun j hj => factor_nonzero i j)
  have hscale : scale ≠ 0 := by
    dsimp [scale]
    apply inv_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact_mod_cast Nat.factorial_ne_zero (d i)
  have hP : P.totalDegree = n := by
    rw [show P = MvPolynomial.C scale * Q by
      exact MvPolynomial.smul_eq_C_mul Q scale]
    rw [MvPolynomial.totalDegree_mul_of_isDomain]
    · rw [MvPolynomial.totalDegree_C, hQ, hd, Nat.zero_add]
    · exact (MvPolynomial.C_ne_zero.mpr hscale)
    · dsimp [Q]
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact factor_nonzero i j
  refine ⟨P, hP, ?_, ?_⟩
  · intro x
    rw [show P = MvPolynomial.C scale * Q by
      exact MvPolynomial.smul_eq_C_mul Q scale]
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
    dsimp [Q]
    rw [MvPolynomial.eval_prod]
    simp only [MvPolynomial.eval_prod, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    dsimp [scale]
    simp_rw [falling_eval]
    field_simp
    rw [Finset.prod_mul_distrib, Nat.cast_prod]
  · intro x hx
    rw [show P = MvPolynomial.C scale * Q by
      exact MvPolynomial.smul_eq_C_mul Q scale]
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
    dsimp [Q]
    rw [MvPolynomial.eval_prod]
    simp only [MvPolynomial.eval_prod, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    dsimp [scale]
    simp_rw [falling_eval]
    field_simp
    rw [Finset.prod_mul_distrib]
    have hindicator := indicator_eval n d x hd hx
    congr 1
    exact_mod_cast hindicator

end MathlibPlus.Combinatorics
