import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.GammaAssembly

/--
Claim 10579.  A finite-support nonnegative family whose rising-factorial
moments are all one is the point mass at zero.  The finite set `s` is merely a
carrier for the finite sums; `hsupport` says that it contains the whole
support.
-/
theorem gammaAssemblyCollapse_claim10579
    (α : ℝ) (hα : 0 < α) (w : ℕ → ℝ) (s : Finset ℕ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hsupport : ∀ p, p ∉ s → w p = 0)
    (hmoment : ∀ q : ℕ,
      (∑ p ∈ s, w p * (ascPochhammer ℝ p).eval (α + q)) = 1) :
    w 0 = 1 ∧ ∀ p : ℕ, 1 ≤ p → w p = 0 := by
  have hpoch_diff (p : ℕ) (hp : 1 ≤ p) :
      (ascPochhammer ℝ p).eval (α + 1) -
          (ascPochhammer ℝ p).eval α =
        (p : ℝ) * (ascPochhammer ℝ (p - 1)).eval (α + 1) := by
    cases p with
    | zero => omega
    | succ q =>
        have h := congrArg (fun r : Polynomial ℝ => r.eval α)
          (ascPochhammer_succ_comp_X_add_one (S := ℝ) q)
        have h' :
            (ascPochhammer ℝ (q + 1)).eval (α + 1) =
              (ascPochhammer ℝ (q + 1)).eval α +
                (q + 1 : ℝ) * (ascPochhammer ℝ q).eval (α + 1) := by
          simpa [Polynomial.eval_comp] using h
        norm_num [Nat.cast_add, Nat.cast_one] at h' ⊢
        linarith
  have hpoch_diff_pos (p : ℕ) (hp : 1 ≤ p) :
      0 < (ascPochhammer ℝ p).eval (α + 1) -
          (ascPochhammer ℝ p).eval α := by
    rw [hpoch_diff p hp]
    exact mul_pos (by exact_mod_cast hp)
      (ascPochhammer_pos (p - 1) (α + 1) (by linarith))
  have hdiff :
      ∑ p ∈ s, w p *
          ((ascPochhammer ℝ p).eval (α + 1) -
            (ascPochhammer ℝ p).eval α) = 0 := by
    calc
      ∑ p ∈ s, w p *
          ((ascPochhammer ℝ p).eval (α + 1) -
            (ascPochhammer ℝ p).eval α) =
          (∑ p ∈ s, w p * (ascPochhammer ℝ p).eval (α + 1)) -
            ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval α := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by
        have h1 : ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval (α + 1) = 1 := by
          simpa using hmoment 1
        have h0 : ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval α = 1 := by
          simpa using hmoment 0
        rw [h1, h0]
      _ = 0 := sub_self 1
  have hdiff_nonneg : ∀ p ∈ s, 0 ≤ w p *
      ((ascPochhammer ℝ p).eval (α + 1) -
        (ascPochhammer ℝ p).eval α) := by
    intro p hp
    exact mul_nonneg (hw_nonneg p) (by
      cases p with
      | zero => simp
      | succ p =>
          exact (hpoch_diff_pos (p + 1) (by omega)).le)
  have hterm_zero : ∀ p ∈ s, w p *
      ((ascPochhammer ℝ p).eval (α + 1) -
        (ascPochhammer ℝ p).eval α) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiff
  have hw_pos : ∀ p : ℕ, 1 ≤ p → w p = 0 := by
    intro p hp
    by_cases hps : p ∈ s
    · have hterm := hterm_zero p hps
      rcases mul_eq_zero.mp hterm with hw | hd
      · exact hw
      · have hdpos : 0 <
            (ascPochhammer ℝ p).eval (α + 1) -
              (ascPochhammer ℝ p).eval α := by
          exact hpoch_diff_pos p hp
        exact False.elim ((ne_of_gt hdpos) hd)
    · exact hsupport p hps
  have hw_nonzero : ∀ p : ℕ, p ≠ 0 → w p = 0 := by
    intro p hp
    exact hw_pos p (Nat.one_le_iff_ne_zero.mpr hp)
  have hw0 : w 0 = 1 := by
    by_cases h0 : 0 ∈ s
    · have hsingle :
          ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval α =
            w 0 * (ascPochhammer ℝ 0).eval α := by
        apply Finset.sum_eq_single 0
        · intro b hb hne
          simp [hw_nonzero b hne]
        · intro hnot
          exact False.elim (hnot h0)
      have h : ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval α = 1 := by
        simpa using hmoment 0
      rw [hsingle] at h
      simpa using h
    · have hzero : ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval α = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hp0 : p ≠ 0 := by
          intro hpz
          exact h0 (hpz ▸ hp)
        simp [hw_nonzero p hp0]
      have h : ∑ p ∈ s, w p * (ascPochhammer ℝ p).eval α = 1 := by
        simpa using hmoment 0
      rw [hzero] at h
      norm_num at h
  exact ⟨hw0, hw_pos⟩

end MathlibPlus.Algebra.GammaAssembly

namespace MathlibPlus.Algebra.WeightedBlockComposition

/-- Claim 26597's weighted block law is associative over any semiring. -/
theorem weightedBlockComposition_associative_claim26597
    {R : Type*} [Semiring R] (left middle right : R × R) :
    let compose : R × R → R × R → R × R :=
      fun right left => (right.1 * left.1, left.2 + right.2 * left.1)
    compose (compose right middle) left = compose right (compose middle left) := by
  dsimp
  apply Prod.ext
  · simp [mul_assoc]
  · simp [mul_assoc, add_assoc, add_mul]

end MathlibPlus.Algebra.WeightedBlockComposition
