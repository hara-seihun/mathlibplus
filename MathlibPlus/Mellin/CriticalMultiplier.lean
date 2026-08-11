import Mathlib

/-!
# Critical Mellin multiplier coordinates

Exact elementary definitions and identities extracted from legacy packet `C-0168`.
The namespace is intentionally specific to the critical Mellin calculation; these
coordinates do not assert any of the packet's explicitly excluded consequences about
hyperbolicity, defect bounds, zeta-phase control, or the Riemann hypothesis.

Lean's real division totalizes the defining formulas at singular inputs. The theorems
whose analytic reading requires `log lambda ≠ 0` or a nonzero phase retain those
hypotheses explicitly.
-/

open Filter Topology

namespace MathlibPlus.Mellin

/-- The packet's leading critical Mellin multiplier, with `L = log λ`. -/
noncomputable def criticalMellinMultiplier (lambda kappa z : ℝ) : ℝ :=
  1 - kappa * (4 * z ^ 2 + 15) /
    (16 * Real.pi ^ 2 * Real.log lambda ^ 2)

/-- The phase coordinate at which completed-zeta decay and a Dini contribution of
order `λ⁻⁵⸍²` have the same exponential scale. -/
noncomputable def gammaDiniPhase (Y : ℝ) : ℝ :=
  (4 / Real.pi) * ((5 : ℝ) / 2 - Y)

/-- The critical scalar coordinate aligned with `gammaDiniPhase Y`. -/
noncomputable def gammaDiniAlignment (Y : ℝ) : ℝ :=
  4 * Real.pi ^ 2 / gammaDiniPhase Y ^ 2

/-- Closed form of the aligned critical coordinate away from its singular height. -/
theorem gammaDiniAlignment_formula (Y : ℝ) (hY : Y ≠ (5 : ℝ) / 2) :
    gammaDiniAlignment Y =
      Real.pi ^ 4 / (4 * ((5 : ℝ) / 2 - Y) ^ 2) := by
  rw [gammaDiniAlignment, gammaDiniPhase]
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hd : (5 : ℝ) / 2 - Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
  field_simp

/-- Along any critical scaling `z r / log (lambda r) → tau`, the multiplier has the
packet's stated limiting residual. -/
theorem criticalMellinMultiplier_scalingLimit
    (kappa tau : ℝ) (lambda z : ℕ → ℝ)
    (hlambda : Tendsto lambda atTop atTop)
    (hscaled : Tendsto (fun r => z r / Real.log (lambda r)) atTop (𝓝 tau)) :
    Tendsto (fun r => criticalMellinMultiplier (lambda r) kappa (z r))
      atTop (𝓝 (1 - kappa * tau ^ 2 / (4 * Real.pi ^ 2))) := by
  have hlog : Tendsto (fun r => Real.log (lambda r)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlambda
  have hinv : Tendsto (fun r => (Real.log (lambda r))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hsmall :
      Tendsto (fun r => 15 * (Real.log (lambda r))⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hinv.pow 2)
  have hcore :
      Tendsto
        (fun r =>
          1 - kappa *
            ((4 * (z r / Real.log (lambda r)) ^ 2 +
                15 * (Real.log (lambda r))⁻¹ ^ 2) /
              (16 * Real.pi ^ 2)))
        atTop (𝓝 (1 - kappa * tau ^ 2 / (4 * Real.pi ^ 2))) := by
    convert tendsto_const_nhds.sub
      (tendsto_const_nhds.mul
        (((tendsto_const_nhds.mul (hscaled.pow 2)).add hsmall).div_const
          (16 * Real.pi ^ 2))) using 1
    congr 1
    ring
  apply hcore.congr'
  filter_upwards [hlambda.eventually (eventually_gt_atTop (1 : ℝ))] with r hr
  have hlog_ne : Real.log (lambda r) ≠ 0 := ne_of_gt (Real.log_pos hr)
  rw [criticalMellinMultiplier]
  field_simp

/-- On the packet's height range, the aligned coordinate is the unique scalar that
cancels the limiting phase-line multiplier. -/
theorem gammaDiniPhase_uniqueCancellation
    (Y kappa : ℝ) (_hY0 : 0 ≤ Y) (hYhalf : Y ≤ (1 : ℝ) / 2) :
    (1 - kappa * gammaDiniPhase Y ^ 2 / (4 * Real.pi ^ 2) = 0 ↔
      kappa = gammaDiniAlignment Y) := by
  have hphase_pos : 0 < gammaDiniPhase Y := by
    rw [gammaDiniPhase]
    have : 0 < (5 : ℝ) / 2 - Y := by linarith
    positivity
  have hphase : gammaDiniPhase Y ≠ 0 := ne_of_gt hphase_pos
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [gammaDiniAlignment]
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [sq_pos_of_ne_zero hphase, sq_pos_of_ne_zero hπ]
  · intro h
    rw [h]
    field_simp
    norm_num

/-- The aligned coordinate tends to `pi ^ 4 / 16` at half height. -/
theorem gammaDiniAlignment_halfHeightLimit :
    Tendsto gammaDiniAlignment (𝓝 ((1 : ℝ) / 2))
      (𝓝 (Real.pi ^ 4 / 16)) := by
  have hphase : gammaDiniPhase ((1 : ℝ) / 2) ≠ 0 := by
    rw [gammaDiniPhase]
    positivity
  have hphase_cont : ContinuousAt gammaDiniPhase ((1 : ℝ) / 2) := by
    unfold gammaDiniPhase
    fun_prop
  have hcont : ContinuousAt gammaDiniAlignment ((1 : ℝ) / 2) := by
    unfold gammaDiniAlignment
    exact continuousAt_const.div₀ (hphase_cont.pow 2) (pow_ne_zero 2 hphase)
  convert hcont.tendsto using 1
  norm_num [gammaDiniAlignment, gammaDiniPhase]
  field_simp
  ring

/-- Every height schedule converging to half height has the same aligned limit. -/
theorem gammaDiniAlignment_heightSchedule
    (Y : ℕ → ℝ) (hY : Tendsto Y atTop (𝓝 ((1 : ℝ) / 2))) :
    Tendsto (fun r => gammaDiniAlignment (Y r)) atTop
      (𝓝 (Real.pi ^ 4 / 16)) :=
  gammaDiniAlignment_halfHeightLimit.comp hY

/-- Exact expansion of the aligned multiplier at an additive shift from the phase
line. No asymptotic or boundedness hypothesis on `w` is needed for the identity. -/
theorem criticalMellinMultiplier_alignedExpansion
    (Y lambda w : ℝ) (hlog : Real.log lambda ≠ 0)
    (hphase : gammaDiniPhase Y ≠ 0) :
    criticalMellinMultiplier lambda (gammaDiniAlignment Y)
        (gammaDiniPhase Y * Real.log lambda + w) =
      -2 * w / (gammaDiniPhase Y * Real.log lambda) -
      (4 * w ^ 2 + 15) /
        (4 * gammaDiniPhase Y ^ 2 * Real.log lambda ^ 2) := by
  rw [criticalMellinMultiplier, gammaDiniAlignment]
  field_simp
  ring

/-- The exact expansion gives a global remainder bound whose constant depends only
on `Y`. This is the stronger reading suggested by the packet's `O_Y` notation. -/
theorem criticalMellinMultiplier_alignedGlobalRemainder
    (Y : ℝ) (hphase : gammaDiniPhase Y ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda w : ℝ,
      Real.exp 1 ≤ lambda →
      |criticalMellinMultiplier lambda (gammaDiniAlignment Y)
          (gammaDiniPhase Y * Real.log lambda + w) +
        2 * w / (gammaDiniPhase Y * Real.log lambda)| ≤
      C * (1 + |w| ^ 2) / Real.log lambda ^ 2 := by
  let phase := gammaDiniPhase Y
  refine ⟨15 / (4 * phase ^ 2), by positivity, ?_⟩
  intro lambda w hlambda
  have hone_lt : (1 : ℝ) < lambda :=
    lt_of_lt_of_le ((Real.one_lt_exp_iff).2 zero_lt_one) hlambda
  have hlog_pos : 0 < Real.log lambda := Real.log_pos hone_lt
  have hlog : Real.log lambda ≠ 0 := ne_of_gt hlog_pos
  have hexp := criticalMellinMultiplier_alignedExpansion Y lambda w hlog hphase
  have hcancel :
      criticalMellinMultiplier lambda (gammaDiniAlignment Y)
          (gammaDiniPhase Y * Real.log lambda + w) +
        2 * w / (gammaDiniPhase Y * Real.log lambda) =
      -(4 * w ^ 2 + 15) /
        (4 * gammaDiniPhase Y ^ 2 * Real.log lambda ^ 2) := by
    rw [hexp]
    ring
  rw [hcancel, abs_div, abs_neg, abs_of_nonneg (by positivity),
    abs_of_pos (by positivity : 0 < 4 * gammaDiniPhase Y ^ 2 * Real.log lambda ^ 2)]
  change
    (4 * w ^ 2 + 15) /
        (4 * phase ^ 2 * Real.log lambda ^ 2) ≤
      (15 / (4 * phase ^ 2)) * (1 + |w| ^ 2) /
        Real.log lambda ^ 2
  have hphase_sq : 0 < phase ^ 2 := sq_pos_of_ne_zero hphase
  have hden_pos : 0 < 4 * phase ^ 2 := mul_pos (by norm_num) hphase_sq
  have hlog_sq : 0 < Real.log lambda ^ 2 := sq_pos_of_pos hlog_pos
  have hfactor :
      (4 * w ^ 2 + 15) / (4 * phase ^ 2 * Real.log lambda ^ 2) =
        ((4 * w ^ 2 + 15) / (4 * phase ^ 2)) / Real.log lambda ^ 2 := by
    field_simp
  rw [hfactor]
  apply (div_le_div_iff_of_pos_right hlog_sq).2
  rw [show (15 / (4 * phase ^ 2)) * (1 + |w| ^ 2) =
      (15 * (1 + |w| ^ 2)) / (4 * phase ^ 2) by field_simp]
  apply (div_le_div_iff_of_pos_right hden_pos).2
  rw [sq_abs]
  nlinarith [sq_nonneg w]

/-- Uniform remainder on each fixed bounded-shift range, preserving the quantifier
order of the packet's displayed Lean draft. -/
theorem criticalMellinMultiplier_alignedUniformRemainder
    (Y W : ℝ) (_hW : 0 ≤ W) (hphase : gammaDiniPhase Y ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda w : ℝ,
      Real.exp 1 ≤ lambda → |w| ≤ W →
      |criticalMellinMultiplier lambda (gammaDiniAlignment Y)
          (gammaDiniPhase Y * Real.log lambda + w) +
        2 * w / (gammaDiniPhase Y * Real.log lambda)| ≤
      C * (1 + |w| ^ 2) / Real.log lambda ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    criticalMellinMultiplier_alignedGlobalRemainder Y hphase
  exact ⟨C, hC, fun lambda w hlambda _hw => hbound lambda w hlambda⟩

/-- On the packet's height range the phase-line residual is exactly
`1 - kappa / gammaDiniAlignment Y`, and is nonzero off the aligned coordinate. -/
theorem gammaDiniPhase_nonalignedResidual
    (Y kappa : ℝ) (hY0 : 0 ≤ Y) (hYhalf : Y ≤ (1 : ℝ) / 2) :
    1 - kappa * gammaDiniPhase Y ^ 2 / (4 * Real.pi ^ 2) =
        1 - kappa / gammaDiniAlignment Y ∧
      (kappa ≠ gammaDiniAlignment Y →
        1 - kappa / gammaDiniAlignment Y ≠ 0) := by
  have hphase_pos : 0 < gammaDiniPhase Y := by
    rw [gammaDiniPhase]
    have : 0 < (5 : ℝ) / 2 - Y := by linarith
    positivity
  have hphase : gammaDiniPhase Y ≠ 0 := ne_of_gt hphase_pos
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have halign : gammaDiniAlignment Y ≠ 0 := by
    rw [gammaDiniAlignment]
    positivity
  have hresidual :
      1 - kappa * gammaDiniPhase Y ^ 2 / (4 * Real.pi ^ 2) =
        1 - kappa / gammaDiniAlignment Y := by
    rw [gammaDiniAlignment]
    field_simp
  refine ⟨hresidual, ?_⟩
  intro hkappa hzero
  apply hkappa
  apply (gammaDiniPhase_uniqueCancellation Y kappa hY0 hYhalf).mp
  rw [hresidual, hzero]

end MathlibPlus.Mellin
