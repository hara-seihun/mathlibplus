import MathlibPlus.Basic

namespace MathlibPlus.Analysis.AdmittedClaimCalculus

/-!
Formalizations of three exact calculus identities from admitted claims.

The source statements omit some local parameters.  They are made explicit
here rather than hidden: the packet rate parameters are positive, the
potential is differentiated on its positive domain, and the Lambert residual
uses the defining equation for the positive Lambert value.
-/

/--
Claim 42079.  The derivative-corrected logistic packet has the displayed
endpoint value and vanishing first derivative.  The two positive parameters
are the logistic rate `d` and boundary rate `a`.
-/
theorem correctedPacketEndpointIdentities_claim42079 {d a : ℝ}
    (_hd : 0 < d) (ha : 0 < a) :
    let lam : ℝ := d / (2 * a)
    let q : ℝ → ℝ := fun u =>
      (1 - lam + lam * Real.exp (-a * u)) / (1 + Real.exp (-d * u))
    q 0 = 1 / 2 ∧ HasDerivAt q 0 0 := by
  dsimp
  have hexp_a : HasDerivAt (fun u : ℝ => Real.exp (-a * u)) (-a) 0 := by
    have hinner : HasDerivAt (fun u : ℝ => -a * u) (-a) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-a)
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-a * (0 : ℝ))).comp 0 hinner
  have hexp_d : HasDerivAt (fun u : ℝ => Real.exp (-d * u)) (-d) 0 := by
    have hinner : HasDerivAt (fun u : ℝ => -d * u) (-d) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-d)
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-d * (0 : ℝ))).comp 0 hinner
  have hnum :
      HasDerivAt
        (fun u : ℝ => 1 - d / (2 * a) + (d / (2 * a)) * Real.exp (-a * u))
        ((d / (2 * a)) * (-a)) 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => 1 - d / (2 * a)) 0 0 :=
      hasDerivAt_const (0 : ℝ) _
    have hmul := (hasDerivAt_const (0 : ℝ) (d / (2 * a))).mul hexp_a
    have hadd := hconst.add hmul
    have hfun :
        (fun x : ℝ => 1 - d / (2 * a)) +
            (fun x : ℝ => d / (2 * a)) * (fun u : ℝ => Real.exp (-a * u)) =
          (fun u : ℝ => 1 - d / (2 * a) + (d / (2 * a)) * Real.exp (-a * u)) := by
      funext u
      rfl
    rw [hfun] at hadd
    simpa [zero_add, zero_mul, mul_zero] using hadd
  have hden :
      HasDerivAt (fun u : ℝ => 1 + Real.exp (-d * u)) (-d) 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 :=
      hasDerivAt_const (0 : ℝ) _
    have hadd := hconst.add hexp_d
    have hfun :
        (fun x : ℝ => (1 : ℝ)) + (fun u : ℝ => Real.exp (-d * u)) =
          (fun u : ℝ => 1 + Real.exp (-d * u)) := by
      funext u
      rfl
    rw [hfun] at hadd
    simpa [zero_add] using hadd
  have hq := hnum.div hden (by norm_num : (1 + Real.exp (-d * (0 : ℝ))) ≠ 0)
  constructor
  · norm_num
  · have hderiv :
        ((d / (2 * a)) * (-a) * (1 + Real.exp (-d * (0 : ℝ))) -
          (1 - d / (2 * a) + (d / (2 * a)) * Real.exp (-a * (0 : ℝ))) * (-d)) /
          (1 + Real.exp (-d * (0 : ℝ))) ^ 2 = 0 := by
      norm_num
      field_simp
      ring
    have hfun :
        (fun u : ℝ => 1 - d / (2 * a) + (d / (2 * a)) * Real.exp (-a * u)) /
            (fun u : ℝ => 1 + Real.exp (-d * u)) =
          (fun u : ℝ =>
            (1 - d / (2 * a) + (d / (2 * a)) * Real.exp (-a * u)) /
              (1 + Real.exp (-d * u))) := by
      funext u
      rfl
    rw [hfun, hderiv] at hq
    exact hq

/--
Claim 8929.  On the natural positive domain, the displayed filling potential
has the transform in Record 13 as its derivative.
-/
theorem explicitPotentialHasDerivAt_claim8929 {b s : ℝ}
    (hb : 0 < b) (hs : 0 < s) :
    HasDerivAt
      (fun t : ℝ =>
        2 * Real.arsinh (Real.sqrt t / b) -
          2 * Real.sqrt t / (Real.sqrt (t + b ^ 2) + b))
      (1 / (Real.sqrt s * (Real.sqrt (s + b ^ 2) + b))) s := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hsb : 0 < s + b ^ 2 := by positivity
  have hsb0 : s + b ^ 2 ≠ 0 := ne_of_gt hsb
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsbsqrt : 0 < Real.sqrt (s + b ^ 2) := Real.sqrt_pos.2 hsb
  have hx : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt s)) s :=
    Real.hasDerivAt_sqrt hs0
  have hy :
      HasDerivAt (fun t : ℝ => Real.sqrt (t + b ^ 2))
        (1 / (2 * Real.sqrt (s + b ^ 2))) s := by
    have hinner : HasDerivAt (fun t : ℝ => t + b ^ 2) 1 s :=
      (hasDerivAt_id s).add_const _
    simpa [Function.comp_def] using (Real.hasDerivAt_sqrt hsb0).comp s hinner
  have harg :
      HasDerivAt (fun t : ℝ => Real.sqrt t / b)
        ((1 / (2 * Real.sqrt s)) / b) s := by
    simpa using hx.div_const b
  have harsinh :
      HasDerivAt (fun t : ℝ => Real.arsinh (Real.sqrt t / b))
        ((Real.sqrt (1 + (Real.sqrt s / b) ^ 2))⁻¹ *
          ((1 / (2 * Real.sqrt s)) / b)) s := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_arsinh (Real.sqrt s / b)).comp s harg
  have hfirst :
      HasDerivAt (fun t : ℝ => 2 * Real.arsinh (Real.sqrt t / b))
        (2 * ((Real.sqrt (1 + (Real.sqrt s / b) ^ 2))⁻¹ *
          ((1 / (2 * Real.sqrt s)) / b))) s := by
    simpa [Function.comp_def] using harsinh.const_mul 2
  have hden :
      HasDerivAt (fun t : ℝ => Real.sqrt (t + b ^ 2) + b)
        (1 / (2 * Real.sqrt (s + b ^ 2))) s := by
    simpa using hy.add_const b
  have hquot := hx.div hden (by positivity : Real.sqrt (s + b ^ 2) + b ≠ 0)
  have hsecond :
      HasDerivAt
        (fun t : ℝ =>
          2 * (Real.sqrt t * (Real.sqrt (t + b ^ 2) + b)⁻¹))
        (2 * (((1 / (2 * Real.sqrt s)) * (Real.sqrt (s + b ^ 2) + b) -
          Real.sqrt s * (1 / (2 * Real.sqrt (s + b ^ 2)))) *
          (Real.sqrt (s + b ^ 2) + b)⁻¹ ^ 2)) s := by
    have hmul := hquot.const_mul 2
    have hfun :
        (fun y : ℝ =>
          2 * ((fun t : ℝ => Real.sqrt t) /
            (fun t : ℝ => Real.sqrt (t + b ^ 2) + b)) y) =
          (fun t : ℝ =>
            2 * (Real.sqrt t * (Real.sqrt (t + b ^ 2) + b)⁻¹)) := by
      funext t
      simp only [Pi.div_apply, div_eq_mul_inv]
    rw [hfun] at hmul
    simpa [div_eq_mul_inv, inv_pow] using hmul
  have hroot : Real.sqrt (1 + (Real.sqrt s / b) ^ 2) = Real.sqrt (s + b ^ 2) / b := by
    have harg_eq : 1 + (Real.sqrt s / b) ^ 2 = (s + b ^ 2) / b ^ 2 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hs)]
      field_simp
      ring
    rw [harg_eq, Real.sqrt_div (by positivity), Real.sqrt_sq hb.le]
  have hcalc :
      2 * ((Real.sqrt (1 + (Real.sqrt s / b) ^ 2))⁻¹ *
          ((1 / (2 * Real.sqrt s)) / b)) -
        2 * (((1 / (2 * Real.sqrt s)) * (Real.sqrt (s + b ^ 2) + b) -
          Real.sqrt s * (1 / (2 * Real.sqrt (s + b ^ 2)))) *
          (Real.sqrt (s + b ^ 2) + b)⁻¹ ^ 2) =
        1 / (Real.sqrt s * (Real.sqrt (s + b ^ 2) + b)) := by
    rw [hroot]
    have hsquare : Real.sqrt s ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
    have hsb_square : Real.sqrt (s + b ^ 2) ^ 2 = s + b ^ 2 :=
      Real.sq_sqrt (le_of_lt hsb)
    field_simp [hs0, hb0, hsb0]
    nlinarith
  have htotal := hfirst.sub hsecond
  have hfun :
      (fun t : ℝ => 2 * Real.arsinh (Real.sqrt t / b)) -
          (fun t : ℝ =>
            2 * (Real.sqrt t * (Real.sqrt (t + b ^ 2) + b)⁻¹)) =
        (fun t : ℝ =>
          2 * Real.arsinh (Real.sqrt t / b) -
            2 * Real.sqrt t / (Real.sqrt (t + b ^ 2) + b)) := by
    funext t
    simp only [Pi.sub_apply, div_eq_mul_inv]
    ring
  rw [hfun, hcalc] at htotal
  exact htotal

/--
Claim 8818.  The Lambert-gauge residual is written with its defining
relation `W exp W = j/(2π)` made explicit.
-/
theorem additiveResidualFormula_claim8818 {j : ℕ} {a W : ℝ}
    (hj : 0 < j) (ha : 0 < a) (_hW : 0 < W)
    (hLambert : W * Real.exp W = (j : ℝ) / (2 * Real.pi)) :
    let R : ℝ := Real.log (8 * Real.pi * a) + W
    4 * (j : ℝ) * a - W = W * (Real.exp R - 1) := by
  dsimp
  have harg : (0 : ℝ) < 8 * Real.pi * a := by positivity
  rw [Real.exp_add, Real.exp_log harg]
  have hscaled : W * (8 * Real.pi * a * Real.exp W) = 4 * (j : ℝ) * a := by
    calc
      W * (8 * Real.pi * a * Real.exp W) =
          (8 * Real.pi * a) * (W * Real.exp W) := by ring
      _ = 4 * (j : ℝ) * a := by rw [hLambert]; field_simp; ring
  calc
    4 * (j : ℝ) * a - W = W * (8 * Real.pi * a * Real.exp W) - W := by rw [hscaled]
    _ = W * (8 * Real.pi * a * Real.exp W - 1) := by ring

end MathlibPlus.Analysis.AdmittedClaimCalculus
