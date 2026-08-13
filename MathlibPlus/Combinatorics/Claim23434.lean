import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

private lemma claim23434_factor_degree_sub {σ : Type*} [DecidableEq σ]
    (k : σ) (a : ℚ) :
    (MvPolynomial.X k - MvPolynomial.C a : MvPolynomial σ ℚ).totalDegree ≤ 1 := by
  calc
    (MvPolynomial.X k - MvPolynomial.C a : MvPolynomial σ ℚ).totalDegree ≤
        (MvPolynomial.X k : MvPolynomial σ ℚ).totalDegree :=
      MvPolynomial.totalDegree_sub_C_le _ _
    _ = 1 := by simp

/--
Claim 23434: if a finite family of distinct rational vectors has cardinality at
most four, each member is separated from the others by a rational multivariate
interpolant of total degree at most its family cardinality minus one (and hence
at most three).  The ambient vector space is represented as the finitely
supported-polynomial coordinate type `σ → ℚ`; no coordinate dimension is fixed.
-/
theorem claim23434_degree_three_interpolation
    {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → σ → ℚ) (hx : Function.Injective x)
    (hcard : Fintype.card ι ≤ 4) :
    ∀ i : ι, ∃ P : MvPolynomial σ ℚ,
      P.totalDegree ≤ Fintype.card ι - 1 ∧
      P.totalDegree ≤ 3 ∧
      ∀ j : ι, MvPolynomial.eval (x j) P = if j = i then 1 else 0 := by
  classical
  have sep_exists (i j : ι) (hij : i ≠ j) : ∃ k : σ, x i k ≠ x j k := by
    by_contra h
    apply hij
    apply hx
    funext k
    by_contra hne
    exact h ⟨k, hne⟩
  let sep (i j : ι) (hij : i ≠ j) : σ :=
    Classical.choose (sep_exists i j hij)
  have hsep (i j : ι) (hij : i ≠ j) :
      x i (sep i j hij) ≠ x j (sep i j hij) := by
    dsimp [sep]
    exact Classical.choose_spec (sep_exists i j hij)
  let factor (i j : ι) : MvPolynomial σ ℚ :=
    if h : i = j then 1 else
      MvPolynomial.C ((x i (sep i j h) - x j (sep i j h))⁻¹) *
        (MvPolynomial.X (sep i j h) -
          MvPolynomial.C (x j (sep i j h)))
  have hfactor_degree (i j : ι) : (factor i j).totalDegree ≤ 1 := by
    by_cases hij : i = j
    · simp [factor, hij]
    · dsimp [factor]
      rw [dif_neg hij]
      calc
        (MvPolynomial.C ((x i (sep i j hij) - x j (sep i j hij))⁻¹) *
            (MvPolynomial.X (sep i j hij) -
              MvPolynomial.C (x j (sep i j hij)))).totalDegree ≤
            (MvPolynomial.C ((x i (sep i j hij) - x j (sep i j hij))⁻¹) :
              MvPolynomial σ ℚ).totalDegree +
            (MvPolynomial.X (sep i j hij) -
              MvPolynomial.C (x j (sep i j hij)) : MvPolynomial σ ℚ).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 0 + (MvPolynomial.X (sep i j hij) -
              MvPolynomial.C (x j (sep i j hij)) : MvPolynomial σ ℚ).totalDegree := by
          simp
        _ ≤ 1 := by
          simpa using claim23434_factor_degree_sub
            (sep i j hij) (x j (sep i j hij))
  have hfactor_self (i j : ι) (hij : i ≠ j) :
      MvPolynomial.eval (x i) (factor i j) = 1 := by
    simp only [factor, dif_neg hij, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_sub, MvPolynomial.eval_X]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep i j hij))
  have hfactor_other (i j : ι) (hij : i ≠ j) :
      MvPolynomial.eval (x j) (factor i j) = 0 := by
    simp [factor, hij]
  intro i
  let P : MvPolynomial σ ℚ :=
    ∏ j ∈ (Finset.univ.erase i), factor i j
  have hPdegree : P.totalDegree ≤ Fintype.card ι - 1 := by
    dsimp [P]
    calc
      (∏ j ∈ (Finset.univ.erase i), factor i j).totalDegree ≤
          ∑ j ∈ (Finset.univ.erase i), (factor i j).totalDegree := by
        simpa using MvPolynomial.totalDegree_finsetProd
          (Finset.univ.erase i) (factor i)
      _ ≤ ∑ _j ∈ (Finset.univ.erase i), 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfactor_degree i j
      _ = Fintype.card ι - 1 := by simp
  have hPsmall : P.totalDegree ≤ 3 := by
    exact hPdegree.trans (by omega)
  refine ⟨P, hPdegree, hPsmall, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    dsimp [P]
    rw [MvPolynomial.eval_prod]
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro k hk
    exact hfactor_self i k (Ne.symm (Finset.mem_erase.mp hk).1)
  · dsimp [P]
    rw [MvPolynomial.eval_prod]
    rw [if_neg hji]
    refine Finset.prod_eq_zero (i := j) (by simp [hji]) ?_
    exact hfactor_other i j (Ne.symm hji)

end MathlibPlus.Combinatorics
