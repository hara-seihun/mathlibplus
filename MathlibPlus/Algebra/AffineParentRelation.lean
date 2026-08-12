import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 26869: a nontrivial affine relation among three distinct parents has
all coefficients nonzero, and injectivity of the parent map carries it to the
corresponding child-product relation. -/
theorem affineParentRelation_descends_claim26869
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W]
    (J : V →ₗ[ℚ] W) (hJ : Function.Injective J)
    (P : Fin 3 → V) (hP : Pairwise (fun i j => P i ≠ P j))
    (c : Fin 3 → ℚ)
    (hAffine : ∑ i, c i • J (P i) = 0)
    (hSum : ∑ i, c i = 0)
    (hNontrivial : ∃ i, c i ≠ 0) :
    (∀ i, c i ≠ 0) ∧ ∑ i, c i • P i = 0 := by
  have hChild : ∑ i, c i • P i = 0 := by
    apply hJ
    rw [map_zero, map_sum]
    simp only [map_smul]
    exact hAffine
  have hNonzero (i : Fin 3) : c i ≠ 0 := by
    fin_cases i
    · intro hc0
      have hc0' : c 0 = 0 := by simpa using hc0
      have hsum : c 1 + c 2 = 0 := by
        simpa [Fin.sum_univ_succ, hc0'] using hSum
      have hrel : c 1 • P 1 + c 2 • P 2 = 0 := by
        simpa [Fin.sum_univ_succ, hc0'] using hChild
      have hrel' : c 1 • (P 1 - P 2) = 0 := by
        have hc2 : c 2 = -c 1 := by linarith [hsum]
        calc
          c 1 • (P 1 - P 2) = c 1 • P 1 + (-c 1) • P 2 := by
            rw [smul_sub, sub_eq_add_neg, neg_smul]
          _ = c 1 • P 1 + c 2 • P 2 := by rw [← hc2]
          _ = 0 := hrel
      rcases smul_eq_zero.mp hrel' with hc1 | hP12
      · have hc2zero : c 2 = 0 := by linarith [hsum]
        have hallzero : ∀ i, c i = 0 := by
          intro i
          fin_cases i
          · exact hc0'
          · exact hc1
          · exact hc2zero
        rcases hNontrivial with ⟨i, hi⟩
        exact hi (hallzero i)
      · exact (hP (by decide)) (sub_eq_zero.mp hP12)
    · intro hc1
      have hc1' : c 1 = 0 := by simpa using hc1
      have hsum : c 0 + c 2 = 0 := by
        simpa [Fin.sum_univ_succ, hc1'] using hSum
      have hrel : c 0 • P 0 + c 2 • P 2 = 0 := by
        simpa [Fin.sum_univ_succ, hc1'] using hChild
      have hrel' : c 0 • (P 0 - P 2) = 0 := by
        have hc2 : c 2 = -c 0 := by linarith [hsum]
        calc
          c 0 • (P 0 - P 2) = c 0 • P 0 + (-c 0) • P 2 := by
            rw [smul_sub, sub_eq_add_neg, neg_smul]
          _ = c 0 • P 0 + c 2 • P 2 := by rw [← hc2]
          _ = 0 := hrel
      rcases smul_eq_zero.mp hrel' with hc0 | hP02
      · have hc2zero : c 2 = 0 := by linarith [hsum]
        have hallzero : ∀ i, c i = 0 := by
          intro i
          fin_cases i
          · exact hc0
          · exact hc1'
          · exact hc2zero
        rcases hNontrivial with ⟨i, hi⟩
        exact hi (hallzero i)
      · exact (hP (by decide)) (sub_eq_zero.mp hP02)
    · intro hc2
      have hc2' : c 2 = 0 := by simpa using hc2
      have hsum : c 0 + c 1 = 0 := by
        simpa [Fin.sum_univ_succ, hc2'] using hSum
      have hrel : c 0 • P 0 + c 1 • P 1 = 0 := by
        simpa [Fin.sum_univ_succ, hc2'] using hChild
      have hrel' : c 0 • (P 0 - P 1) = 0 := by
        have hc1 : c 1 = -c 0 := by linarith [hsum]
        calc
          c 0 • (P 0 - P 1) = c 0 • P 0 + (-c 0) • P 1 := by
            rw [smul_sub, sub_eq_add_neg, neg_smul]
          _ = c 0 • P 0 + c 1 • P 1 := by rw [← hc1]
          _ = 0 := hrel
      rcases smul_eq_zero.mp hrel' with hc0 | hP01
      · have hc1zero : c 1 = 0 := by linarith [hsum]
        have hallzero : ∀ i, c i = 0 := by
          intro i
          fin_cases i
          · exact hc0
          · exact hc1zero
          · exact hc2'
        rcases hNontrivial with ⟨i, hi⟩
        exact hi (hallzero i)
      · exact (hP (by decide)) (sub_eq_zero.mp hP01)
  exact ⟨hNonzero, hChild⟩

end MathlibPlus.Algebra
