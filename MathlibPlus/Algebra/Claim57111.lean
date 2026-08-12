import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Tactic

open Polynomial

namespace MathlibPlus.Algebra

/-- Exact sign, real-root, and Mahler-measure consequences for the corrected
sixth-degree candidate from admitted claim 57111. -/
theorem correctionDegreeSix_claim57111 :
    let pR : ℝ[X] :=
      X ^ 6 + 2 * X ^ 5 - X ^ 4 + 3 * X ^ 3 - 2 * X + 1
    let pC : ℂ[X] := pR.map Complex.ofRealHom
    pR.eval (-(14 : ℝ) / 5) > 0 ∧
      pR.eval (-(27 : ℝ) / 10) < 0 ∧
      (∃ x : ℝ, x ∈ Set.Ioo (-(14 : ℝ) / 5) (-(27 : ℝ) / 10) ∧
        pR.eval x = 0) ∧
      pC.mahlerMeasure > (27 : ℝ) / 10 := by
  let pR : ℝ[X] :=
    X ^ 6 + 2 * X ^ 5 - X ^ 4 + 3 * X ^ 3 - 2 * X + 1
  let pC : ℂ[X] := pR.map Complex.ofRealHom
  have hsign :
      pR.eval (-(14 : ℝ) / 5) > 0 ∧
        pR.eval (-(27 : ℝ) / 10) < 0 := by
    norm_num [pR, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
  have hab : -(14 : ℝ) / 5 ≤ -(27 : ℝ) / 10 := by norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc
      (pR.eval (-(27 : ℝ) / 10)) (pR.eval (-(14 : ℝ) / 5)) :=
    ⟨le_of_lt hsign.2, le_of_lt hsign.1⟩
  have hroot : ∃ x : ℝ,
      x ∈ Set.Ioo (-(14 : ℝ) / 5) (-(27 : ℝ) / 10) ∧ pR.eval x = 0 := by
    rcases intermediate_value_Icc'
        hab pR.continuous.continuousOn hzero with ⟨x, hx, hxeq⟩
    have hleft : -(14 : ℝ) / 5 < x := by
      rcases hx with ⟨hxleft, hxright⟩
      by_contra hnot
      have hxeqleft : x = -(14 : ℝ) / 5 :=
        le_antisymm (le_of_not_gt hnot) hxleft
      rw [hxeqleft] at hxeq
      linarith [hsign.1]
    have hright : x < -(27 : ℝ) / 10 := by
      rcases hx with ⟨hxleft, hxright⟩
      by_contra hnot
      have hxeqright : x = -(27 : ℝ) / 10 :=
        le_antisymm hxright (le_of_not_gt hnot)
      rw [hxeqright] at hxeq
      linarith [hsign.2]
    exact ⟨x, ⟨hleft, hright⟩, hxeq⟩
  have hmahler : pC.mahlerMeasure > (27 : ℝ) / 10 := by
    rcases hroot with ⟨x, hx, hxzero⟩
    have hpR : pR ≠ 0 := by
      intro h
      have hc := congrArg (fun q : ℝ[X] => q.coeff 6) h
      simp [pR, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] at hc
    have hpC : pC ≠ 0 := by
      intro h
      apply hpR
      apply (Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).mp
      exact h
    have hrootC : Complex.ofReal x ∈ pC.roots := by
      apply (Polynomial.mem_roots hpC).mpr
      rw [Polynomial.IsRoot.def]
      change (pR.map Complex.ofRealHom).eval (Complex.ofReal x) = 0
      calc
        (pR.map Complex.ofRealHom).eval (Complex.ofReal x) =
            Complex.ofReal (pR.eval x) :=
          Polynomial.eval_map_apply Complex.ofRealHom x
        _ = 0 := by rw [hxzero]; rfl
    obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hrootC
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
    rw [hs, Multiset.map_cons, Multiset.prod_cons]
    have hrest : 1 ≤ (s.map (fun a : ℂ => max 1 ‖a‖)).prod := by
      apply Multiset.one_le_prod
      intro a ha
      rcases Multiset.mem_map.mp ha with ⟨z, hz, rfl⟩
      exact le_max_left _ _
    have hfactor : (27 : ℝ) / 10 < max 1 ‖Complex.ofReal x‖ := by
      rw [Complex.norm_real]
      have hxabs : (27 : ℝ) / 10 < |x| := by
        rw [abs_of_neg (by linarith [hx.2] : x < 0)]
        linarith [hx.2]
      exact lt_of_lt_of_le hxabs (le_max_right _ _)
    have hpRmonic : pR.Monic := by
      let q : ℝ[X] := 2 * X ^ 5 - X ^ 4 + 3 * X ^ 3 - 2 * X + 1
      have hq : q.degree < (6 : WithBot ℕ) := by
        apply (degree_lt_iff_coeff_zero q 6).2
        intro m hm
        have hm0 : m ≠ 0 := by omega
        have hm3 : m ≠ 3 := by omega
        have hm4 : m ≠ 4 := by omega
        have hm5 : m ≠ 5 := by omega
        simp [q, Polynomial.coeff_add, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one,
          hm0, hm3, hm4, hm5]
        omega
      have hpdecomp : pR = X ^ 6 + q := by
        dsimp [pR, q]
        ring
      rw [hpdecomp]
      exact monic_X_pow_add hq
    have hpCmonic : pC.Monic := hpRmonic.map Complex.ofRealHom
    have hlc : ‖pC.leadingCoeff‖ = 1 := by
      rw [hpCmonic.leadingCoeff]
      norm_num
    rw [hlc]
    have hfactor_nonneg : 0 ≤ max 1 ‖Complex.ofReal x‖ :=
      le_trans (by norm_num) (le_max_left _ _)
    have hmul : max 1 ‖Complex.ofReal x‖ * 1 ≤
        max 1 ‖Complex.ofReal x‖ *
          (s.map (fun a : ℂ => max 1 ‖a‖)).prod :=
      mul_le_mul_of_nonneg_left hrest hfactor_nonneg
    have hbound : (27 : ℝ) / 10 <
        max 1 ‖Complex.ofReal x‖ *
          (s.map (fun a : ℂ => max 1 ‖a‖)).prod := by
      calc
        (27 : ℝ) / 10 < max 1 ‖Complex.ofReal x‖ := hfactor
        _ = max 1 ‖Complex.ofReal x‖ * 1 := by ring
        _ ≤ max 1 ‖Complex.ofReal x‖ *
            (s.map (fun a : ℂ => max 1 ‖a‖)).prod := hmul
    simpa only [one_mul] using hbound
  exact ⟨hsign.1, hsign.2, hroot, hmahler⟩

end MathlibPlus.Algebra
