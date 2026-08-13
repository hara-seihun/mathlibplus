import Mathlib

namespace MathlibPlus.Analysis.TwoSheetPointKernel

noncomputable section

def lowerSheet (q r : ℝ) : ℝ :=
  r ^ (-(5 / 4 : ℝ)) * Real.exp (-q / r)

def upperSheet (q r : ℝ) : ℝ :=
  r ^ (5 / 4 : ℝ) * Real.exp (-q * r)

def twoSheetKernel (q r : ℝ) : ℝ :=
  lowerSheet q r + upperSheet q r

def centralKernel (q t : ℝ) : ℝ :=
  2 * Real.exp (-q * Real.cosh t)
    * Real.cosh (5 * t / 4 - q * Real.sinh t)

def spectralMode (weight rate q : ℝ) : ℝ :=
  weight * Real.exp (-q * rate)

theorem hasDerivAt_spectralMode
    (weight rate q : ℝ) :
    HasDerivAt (fun x : ℝ => spectralMode weight rate x)
      (-weight * rate * Real.exp (-q * rate)) q := by
  have hinner :
      HasDerivAt (fun x : ℝ => -x * rate) (-rate) q := by
    simpa only [Function.id_def, neg_mul, mul_neg, one_mul] using
      (hasDerivAt_id q).mul_const (-rate)
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x * rate))
      (Real.exp (-q * rate) * (-rate)) q := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-q * rate)).comp q hinner
  simpa [spectralMode, mul_assoc, mul_comm, mul_left_comm] using
    hexp.const_mul weight

theorem deriv_spectralMode (weight rate : ℝ) :
    deriv (fun q : ℝ => spectralMode weight rate q)
      = fun q => -weight * rate * Real.exp (-q * rate) := by
  funext q
  exact (hasDerivAt_spectralMode weight rate q).deriv

theorem secondDeriv_spectralMode (weight rate : ℝ) :
    deriv (deriv (fun q : ℝ => spectralMode weight rate q))
      = fun q => weight * rate ^ 2 * Real.exp (-q * rate) := by
  calc
    deriv (deriv (fun q : ℝ => spectralMode weight rate q))
        = deriv (fun q => -weight * rate * Real.exp (-q * rate)) := by
            rw [deriv_spectralMode]
    _ = deriv (fun q => spectralMode (-weight * rate) rate q) := by
          rfl
    _ = fun q => -(-weight * rate) * rate
        * Real.exp (-q * rate) := by
          rw [deriv_spectralMode]
    _ = fun q => weight * rate ^ 2 * Real.exp (-q * rate) := by
          funext q
          ring

theorem spectralMode_ode
    {weight rate q : ℝ} (hrate : rate ≠ 0) :
    deriv (deriv (fun x : ℝ => spectralMode weight rate x)) q
      + (rate + rate⁻¹)
          * deriv (fun x : ℝ => spectralMode weight rate x) q
      + spectralMode weight rate q = 0 := by
  rw [secondDeriv_spectralMode, deriv_spectralMode]
  dsimp [spectralMode]
  field_simp [hrate]
  ring

theorem twoSheetKernel_eq_spectralModes
    (q r : ℝ) :
    twoSheetKernel q r
      = spectralMode (r ^ (-(5 / 4 : ℝ))) r⁻¹ q
        + spectralMode (r ^ (5 / 4 : ℝ)) r q := by
  simp [twoSheetKernel, lowerSheet, upperSheet, spectralMode,
    div_eq_mul_inv]

theorem twoSheetKernel_spectral_ode
    {q r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun x : ℝ => twoSheetKernel x r)) q
      + (r + r⁻¹) * deriv (fun x : ℝ => twoSheetKernel x r) q
      + twoSheetKernel q r = 0 := by
  have hmode :
      (fun x : ℝ => twoSheetKernel x r)
        = spectralMode (r ^ (-(5 / 4 : ℝ))) r⁻¹
            + spectralMode (r ^ (5 / 4 : ℝ)) r := by
    funext x
    exact twoSheetKernel_eq_spectralModes x r
  have hmodeFirst :
      deriv (fun x : ℝ => twoSheetKernel x r)
        = deriv (spectralMode (r ^ (-(5 / 4 : ℝ))) r⁻¹)
          + deriv (spectralMode (r ^ (5 / 4 : ℝ)) r) := by
    funext x
    rw [hmode]
    exact deriv_add
      (hasDerivAt_spectralMode (r ^ (-(5 / 4 : ℝ))) r⁻¹ x).differentiableAt
      (hasDerivAt_spectralMode (r ^ (5 / 4 : ℝ)) r x).differentiableAt
  have hmodeSecond :
      deriv (deriv (fun x : ℝ => twoSheetKernel x r))
        = deriv (deriv (spectralMode (r ^ (-(5 / 4 : ℝ))) r⁻¹))
          + deriv (deriv (spectralMode (r ^ (5 / 4 : ℝ)) r)) := by
    funext x
    rw [hmodeFirst, deriv_spectralMode, deriv_spectralMode]
    rw [deriv_add]
    · rfl
    · fun_prop
    · fun_prop
  rw [hmodeSecond, hmodeFirst]
  rw [twoSheetKernel_eq_spectralModes]
  have hrInv : r⁻¹ ≠ 0 := by
    exact inv_ne_zero (ne_of_gt hr)
  have hleft := spectralMode_ode (weight := r ^ (-(5 / 4 : ℝ)))
    (rate := r⁻¹) (q := q) hrInv
  have hright := spectralMode_ode (weight := r ^ (5 / 4 : ℝ))
    (rate := r) (q := q) (ne_of_gt hr)
  rw [show (r⁻¹)⁻¹ = r by simp]
    at hleft
  rw [show r⁻¹ + r = r + r⁻¹ by ring] at hleft
  simp only [Pi.add_apply]
  linear_combination hleft + hright

theorem centralKernel_expansion (q t : ℝ) :
    centralKernel q t =
      Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t))
        + Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) := by
  unfold centralKernel
  simp only [Real.cosh_eq, Real.sinh_eq]
  have hfirst :
      2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
            * (Real.exp (5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2)) / 2)
        = Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) := by
    calc
      2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
            * (Real.exp (5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2)) / 2)
          = Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
              * Real.exp (5 * t / 4
                - q * ((Real.exp t - Real.exp (-t)) / 2)) := by ring
      _ = Real.exp
          (-q * ((Real.exp t + Real.exp (-t)) / 2)
            + (5 * t / 4 - q * ((Real.exp t - Real.exp (-t)) / 2))) := by
          rw [← Real.exp_add]
      _ = Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) := by
          congr 1
          ring
  have hsecond :
      2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
          * (Real.exp (-(5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2))) / 2)
        = Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) := by
    calc
      2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
            * (Real.exp (-(5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2))) / 2)
          = Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
              * Real.exp (-(5 * t / 4
                - q * ((Real.exp t - Real.exp (-t)) / 2))) := by ring
      _ = Real.exp
          (-q * ((Real.exp t + Real.exp (-t)) / 2)
            + -(5 * t / 4 - q * ((Real.exp t - Real.exp (-t)) / 2))) := by
          rw [← Real.exp_add]
      _ = Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) := by
          congr 1
          ring
  rw [show
      2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
          * ((Real.exp (5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2))
              + Real.exp (-(5 * t / 4
                - q * ((Real.exp t - Real.exp (-t)) / 2)))) / 2)
        =
      2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
          * (Real.exp (5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2)) / 2)
          + 2 * Real.exp (-q * ((Real.exp t + Real.exp (-t)) / 2))
          * (Real.exp (-(5 * t / 4
              - q * ((Real.exp t - Real.exp (-t)) / 2))) / 2) by ring]
  rw [hfirst, hsecond]
  ring

theorem twoSheetKernel_exp_central (q t : ℝ) :
    twoSheetKernel q (Real.exp t) = centralKernel q t := by
  rw [centralKernel_expansion]
  unfold twoSheetKernel lowerSheet upperSheet
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have hfirst :
      (Real.exp t) ^ (-(5 / 4 : ℝ)) * Real.exp (-q * (Real.exp t)⁻¹)
        = Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) := by
    rw [Real.rpow_def_of_pos hpos]
    simp only [Real.log_exp]
    rw [show (Real.exp t)⁻¹ = Real.exp (-t) by rw [Real.exp_neg]]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsecond :
      (Real.exp t) ^ (5 / 4 : ℝ) * Real.exp (-q * Real.exp t)
        = Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) := by
    rw [Real.rpow_def_of_pos hpos]
    simp only [Real.log_exp]
    rw [← Real.exp_add]
    congr 1
    ring
  change
    (Real.exp t) ^ (-(5 / 4 : ℝ))
          * Real.exp (-q * (Real.exp t)⁻¹)
        + (Real.exp t) ^ (5 / 4 : ℝ)
          * Real.exp (-q * Real.exp t)
      = Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t))
        + Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t)
  rw [hfirst, hsecond]

/-- The central form satisfies the spectral ODE stated in claim 4692. -/
theorem centralKernel_spectral_ode_claim4692 (q t : ℝ) :
    deriv (deriv (fun x : ℝ => centralKernel x t)) q
      + 2 * Real.cosh t * deriv (fun x : ℝ => centralKernel x t) q
      + centralKernel q t = 0 := by
  have hcentral :
      (fun x : ℝ => centralKernel x t)
        = fun x => twoSheetKernel x (Real.exp t) := by
    funext x
    symm
    exact twoSheetKernel_exp_central x t
  rw [hcentral]
  have hode := twoSheetKernel_spectral_ode
    (q := q) (r := Real.exp t) (Real.exp_pos t)
  rw [show centralKernel q t = twoSheetKernel q (Real.exp t) by
    symm
    exact twoSheetKernel_exp_central q t]
  have hcoeff :
      2 * Real.cosh t = Real.exp t + (Real.exp t)⁻¹ := by
    rw [Real.cosh_eq, Real.exp_neg]
    ring
  rw [hcoeff]
  exact hode

/-- In the original `K(q, exp t)` coordinates, this is the claim-4692 ODE. -/
theorem twoSheetKernel_exp_spectral_ode_claim4692 (q t : ℝ) :
    deriv (deriv (fun x : ℝ => twoSheetKernel x (Real.exp t))) q
      + 2 * Real.cosh t *
          deriv (fun x : ℝ => twoSheetKernel x (Real.exp t)) q
      + twoSheetKernel q (Real.exp t) = 0 := by
  have hode := twoSheetKernel_spectral_ode
    (q := q) (r := Real.exp t) (Real.exp_pos t)
  have hcoeff :
      2 * Real.cosh t = Real.exp t + (Real.exp t)⁻¹ := by
    rw [Real.cosh_eq, Real.exp_neg]
    ring
  rw [hcoeff]
  exact hode

end
end MathlibPlus.Analysis.TwoSheetPointKernel
