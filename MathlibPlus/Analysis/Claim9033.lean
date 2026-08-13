import Mathlib

namespace MathlibPlus.Analysis

theorem strictlyConcaveFirstShellPhase_claim9033 (n : ℕ) (hn : 0 < n) :
    let phase : ℝ → ℝ := fun u =>
      2 * (n : ℝ) * Real.log u + u / 2 - Real.pi * Real.exp (2 * u)
    let phaseDeriv : ℝ → ℝ := fun u =>
      2 * (n : ℝ) / u + 1 / 2 - 2 * Real.pi * Real.exp (2 * u)
    (∀ u : ℝ, 0 < u →
      HasDerivAt phase (phaseDeriv u) u ∧
        HasDerivAt phaseDeriv
          (-2 * (n : ℝ) / u ^ 2 - 4 * Real.pi * Real.exp (2 * u)) u ∧
        -2 * (n : ℝ) / u ^ 2 - 4 * Real.pi * Real.exp (2 * u) < 0) ∧
      ∃! u : ℝ, 0 < u ∧ phaseDeriv u = 0 ∧
        2 * (n : ℝ) / u + 1 / 2 = 2 * Real.pi * Real.exp (2 * u) := by
  dsimp
  let g : ℝ → ℝ := fun u =>
    2 * (n : ℝ) / u + 1 / 2 - 2 * Real.pi * Real.exp (2 * u)
  have hg_strict : ∀ {u v : ℝ}, 0 < u → u < v → g v < g u := by
    intro u v hu huv
    have hv : 0 < v := lt_trans hu huv
    have hrecip : 1 / v < (1 / u : ℝ) := one_div_lt_one_div_of_lt hu huv
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfirst : 2 * (n : ℝ) / v < 2 * (n : ℝ) / u := by
      calc
        2 * (n : ℝ) / v = (2 * (n : ℝ)) * (1 / v) := by ring
        _ < (2 * (n : ℝ)) * (1 / u) := by
          exact mul_lt_mul_of_pos_left hrecip (by positivity)
        _ = 2 * (n : ℝ) / u := by ring
    have hexp : Real.exp (2 * u) < Real.exp (2 * v) := by
      apply Real.exp_lt_exp.mpr
      linarith
    have hpi : 0 < (2 : ℝ) * Real.pi := by positivity
    have hsecond :
        2 * Real.pi * Real.exp (2 * u) <
          2 * Real.pi * Real.exp (2 * v) :=
      mul_lt_mul_of_pos_left hexp hpi
    dsimp [g]
    linarith
  have hHcont : Continuous
      (fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ)) := by
    fun_prop
  have hzero_left :
      (fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ)) 0 < 0 := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    norm_num
    linarith
  have hzero_right :
      0 < (fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ)) (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hexp : (1 : ℝ) < Real.exp (2 * (n : ℝ)) := by
      apply Real.one_lt_exp_iff.mpr
      positivity
    have hpiPos : 0 < Real.pi := Real.pi_pos
    have hfirst : 6 * (n : ℝ) < 2 * Real.pi * (n : ℝ) := by
      nlinarith
    have hfactor :
        2 * Real.pi * (n : ℝ) <
          2 * Real.pi * (n : ℝ) * Real.exp (2 * (n : ℝ)) := by
      have hpos : 0 < 2 * Real.pi * (n : ℝ) := by positivity
      nlinarith
    dsimp
    nlinarith
  have hroot : ∃ u : ℝ, 0 < u ∧
      (fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ)) u = 0 := by
    have hle : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hcont : ContinuousOn
        (fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ))
        (Set.Icc 0 (n : ℝ)) := hHcont.continuousOn
    have himage := intermediate_value_Ioc hle hcont
    have hmem :
        0 ∈ Set.Ioc
          ((fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ)) 0)
          ((fun u : ℝ => 2 * Real.pi * u * Real.exp (2 * u) - u / 2 - 2 * (n : ℝ)) (n : ℝ)) :=
      ⟨hzero_left, le_of_lt hzero_right⟩
    rcases himage hmem with ⟨u, hu, hHu⟩
    exact ⟨u, hu.1, hHu⟩
  have hexists : ∃ u : ℝ, 0 < u ∧ g u = 0 := by
    rcases hroot with ⟨u, hu, hHu⟩
    refine ⟨u, hu, ?_⟩
    dsimp [g]
    field_simp [ne_of_gt hu]
    nlinarith [hHu]
  constructor
  · intro u hu
    have hlog := (Real.hasDerivAt_log hu.ne').const_mul (2 * (n : ℝ))
    have hlin := (hasDerivAt_id u).div_const 2
    have hexp_inner : HasDerivAt (fun v : ℝ => Real.exp (2 * v))
        (2 * Real.exp (2 * u)) u := by
      have hinner : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
        simpa using (hasDerivAt_id u).const_mul 2
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (2 * u)).comp u hinner
    have hexp := hexp_inner.const_mul Real.pi
    have hexp_g := hexp_inner.const_mul (2 * Real.pi)
    have hphase := (hlog.add hlin).sub hexp
    have hrecip := (hasDerivAt_const u (2 * (n : ℝ))).div
      (hasDerivAt_id u) hu.ne'
    have hrecip' : HasDerivAt (fun v : ℝ => 2 * (n : ℝ) / v)
        (-2 * (n : ℝ) / u ^ 2) u := by
      have hfun : (fun x : ℝ => 2 * (n : ℝ)) / id =
          (fun v : ℝ => 2 * (n : ℝ) / v) := by
        funext v
        simp
      rw [hfun] at hrecip
      simpa [id_eq, div_eq_mul_inv, inv_pow] using hrecip
    have hlinconst : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 u :=
      hasDerivAt_const u _
    have hphasefun :
        ((fun y : ℝ => 2 * (n : ℝ) * Real.log y) +
            (fun x : ℝ => id x / 2)) -
            (fun y : ℝ => Real.pi * Real.exp (2 * y)) =
          (fun u : ℝ => 2 * (n : ℝ) * Real.log u + u / 2 -
            Real.pi * Real.exp (2 * u)) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    rw [hphasefun] at hphase
    have hphaseDeriv :
        2 * (n : ℝ) * u⁻¹ + 1 / 2 - Real.pi * (2 * Real.exp (2 * u)) =
          2 * (n : ℝ) / u + 1 / 2 - 2 * Real.pi * Real.exp (2 * u) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hphaseDeriv] at hphase
    have hgderiv := (hrecip'.add hlinconst).sub hexp_g
    have hgfun :
        ((fun v : ℝ => 2 * (n : ℝ) / v) +
            (fun _ : ℝ => (1 / 2 : ℝ))) -
            (fun y : ℝ => 2 * Real.pi * Real.exp (2 * y)) =
          (fun u : ℝ => 2 * (n : ℝ) / u + 1 / 2 -
            2 * Real.pi * Real.exp (2 * u)) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [hgfun] at hgderiv
    have hgDerivValue :
        -2 * (n : ℝ) / u ^ 2 + 0 -
            2 * Real.pi * (2 * Real.exp (2 * u)) =
          -2 * (n : ℝ) / u ^ 2 - 4 * Real.pi * Real.exp (2 * u) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hgDerivValue] at hgderiv
    constructor
    · exact hphase
    · constructor
      · exact hgderiv
      · have hterm : 0 < 2 * (n : ℝ) / u ^ 2 := by positivity
        have hexpterm : 0 < 4 * Real.pi * Real.exp (2 * u) := by positivity
        calc
          -2 * (n : ℝ) / u ^ 2 - 4 * Real.pi * Real.exp (2 * u) =
              -(2 * (n : ℝ) / u ^ 2 + 4 * Real.pi * Real.exp (2 * u)) := by ring
          _ < 0 := neg_lt_zero.mpr (add_pos hterm hexpterm)
  · rcases hexists with ⟨u, hu, hgu⟩
    refine ⟨u, ?_, ?_⟩
    · dsimp [g] at hgu ⊢
      exact ⟨hu, hgu, by linarith⟩
    · intro v hv
      rcases hv with ⟨hvpos, hgv, _⟩
      change g v = 0 at hgv
      by_contra hne
      rcases lt_or_gt_of_ne hne with huv | hvu
      · have hlt := hg_strict (u := v) (v := u) hvpos huv
        linarith
      · have hlt := hg_strict (u := u) (v := v) hu hvu
        linarith

end MathlibPlus.Analysis
