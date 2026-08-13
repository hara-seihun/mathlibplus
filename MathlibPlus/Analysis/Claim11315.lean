import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open Set

namespace MathlibPlus.Analysis.Claim11315

/-- For a positive scale, `tanh (u x) / x` decreases strictly on the positive half-line;
its derivative has the sign asserted in claim 11315. -/
theorem strictAntiOn_tanh_mul_div_claim11315 {u : ℝ} (hu : 0 < u) :
    StrictAntiOn (fun x : ℝ => Real.tanh (u * x) / x) (Set.Ioi 0) ∧
      ∀ x ∈ Set.Ioi 0,
        deriv (fun z : ℝ => Real.tanh (u * z) / z) x =
            (u * x / Real.cosh (u * x) ^ 2 - Real.tanh (u * x)) / x ^ 2 ∧
          deriv (fun z : ℝ => Real.tanh (u * z) / z) x < 0 := by
  have hderiv_formula :
      ∀ x ∈ Set.Ioi 0,
        deriv (fun z : ℝ => Real.tanh (u * z) / z) x =
          (u * x / Real.cosh (u * x) ^ 2 - Real.tanh (u * x)) / x ^ 2 := by
    intro x hxpos
    have hux : HasDerivAt (fun z : ℝ => u * z) u x := by
      simpa using (hasDerivAt_id x).const_mul u
    have hsinh : HasDerivAt (fun z : ℝ => Real.sinh (u * z))
        (Real.cosh (u * x) * u) x := hux.sinh
    have hcosh : HasDerivAt (fun z : ℝ => Real.cosh (u * z))
        (Real.sinh (u * x) * u) x := hux.cosh
    have htanh : HasDerivAt (fun z : ℝ => Real.tanh (u * z))
        ((Real.cosh (u * x) * u * Real.cosh (u * x) -
            Real.sinh (u * x) * (Real.sinh (u * x) * u)) /
          Real.cosh (u * x) ^ 2) x := by
      rw [show (fun z : ℝ => Real.tanh (u * z)) =
          (fun z : ℝ => Real.sinh (u * z) / Real.cosh (u * z)) by
            funext z
            rw [Real.tanh_eq_sinh_div_cosh]]
      simpa only [Pi.div_apply] using
        (hsinh.fun_div hcosh (Real.cosh_pos (u * x)).ne')
    have hq := htanh.fun_div (hasDerivAt_id x) (ne_of_gt hxpos)
    have hderiv_raw : deriv (fun z : ℝ => Real.tanh (u * z) / z) x =
        ((Real.cosh (u * x) * u * Real.cosh (u * x) -
            Real.sinh (u * x) * (Real.sinh (u * x) * u)) /
          Real.cosh (u * x) ^ 2 * x - Real.tanh (u * x)) / x ^ 2 := by
      simpa only [Pi.div_apply, id_eq, mul_one] using hq.deriv
    calc
      deriv (fun z : ℝ => Real.tanh (u * z) / z) x =
          ((Real.cosh (u * x) * u * Real.cosh (u * x) -
              Real.sinh (u * x) * (Real.sinh (u * x) * u)) /
            Real.cosh (u * x) ^ 2 * x - Real.tanh (u * x)) / x ^ 2 := hderiv_raw
      _ = (u * x / Real.cosh (u * x) ^ 2 - Real.tanh (u * x)) / x ^ 2 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        field_simp
        rw [Real.cosh_sq_sub_sinh_sq]
        ring
  have hderiv_neg :
      ∀ x ∈ Set.Ioi 0,
        deriv (fun z : ℝ => Real.tanh (u * z) / z) x < 0 := by
    intro x hxpos
    rw [hderiv_formula x hxpos]
    have hypos : 0 < u * x := mul_pos hu hxpos
    have hspos : 0 < Real.sinh (u * x) := Real.sinh_pos_iff.2 hypos
    have hcone : 1 < Real.cosh (u * x) :=
      Real.one_lt_cosh.2 hypos.ne'
    have hslt : u * x < Real.sinh (u * x) :=
      Real.self_lt_sinh_iff.2 hypos
    have hsc : Real.sinh (u * x) < Real.sinh (u * x) * Real.cosh (u * x) := by
      nlinarith
    have hbase : u * x / Real.cosh (u * x) ^ 2 - Real.tanh (u * x) < 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      nlinarith [Real.cosh_sq_sub_sinh_sq (u * x), hslt, hsc]
    exact div_neg_of_neg_of_pos hbase (sq_pos_of_pos hxpos)
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
    · have hmul : Continuous (fun x : ℝ => u * x) :=
        continuous_const.mul continuous_id
      have hs : Continuous (fun x : ℝ => Real.sinh (u * x)) :=
        Real.continuous_sinh.comp hmul
      have hc : Continuous (fun x : ℝ => Real.cosh (u * x)) :=
        Real.continuous_cosh.comp hmul
      rw [show (fun x : ℝ => Real.tanh (u * x) / x) =
          (fun x : ℝ => (Real.sinh (u * x) / Real.cosh (u * x)) / x) by
            funext x
            rw [Real.tanh_eq_sinh_div_cosh]]
      exact (hs.continuousOn.div hc.continuousOn
        (fun x _ => (Real.cosh_pos _).ne')).div continuous_id.continuousOn
        (fun x hx => ne_of_gt hx)
    · intro x hx
      exact hderiv_neg x (by simpa [interior_Ioi] using hx)
  · intro x hx
    exact ⟨hderiv_formula x hx, hderiv_neg x hx⟩

end MathlibPlus.Analysis.Claim11315
