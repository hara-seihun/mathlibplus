import Mathlib

namespace MathlibPlus.Analysis.Claim15256_42871_11628_19365

/-- Claim 15256: the three-part sharp logarithmic exponent inequality. -/
theorem sharpExponentInequality_claim15256
    {η δ : ℝ} (hη : 0 < η) (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    let c : ℝ := η + 1 / 2
    let d : ℝ := c - δ
    2 * Real.log (c / d) < 2 * Real.log (c / η) ∧
      2 * Real.log (c / η) = 2 * Real.log (1 + 1 / (2 * η)) ∧
      2 * Real.log (1 + 1 / (2 * η)) < 1 / η := by
  dsimp
  have hηhalf : 0 < η + 1 / 2 := by linarith
  have hd : 0 < η + 1 / 2 - δ := by linarith
  have hratio : η + 1 / 2 - δ < η + 1 / 2 := by linarith
  have hdiv :
      (η + 1 / 2 - δ) / (η + 1 / 2) < 1 := by
    exact (div_lt_iff₀ hηhalf).2 (by linarith)
  have hratio_pos : 0 <
      (η + 1 / 2 - δ) / (η + 1 / 2) :=
    div_pos hd hηhalf
  have hlog_first :
      Real.log ((η + 1 / 2 - δ) / (η + 1 / 2)) < Real.log 1 :=
    Real.strictMonoOn_log hratio_pos (by norm_num) hdiv
  have hlog_first' :
      Real.log ((η + 1 / 2 - δ) / (η + 1 / 2)) < 0 := by
    simpa using hlog_first
  have hfirst :
      2 * Real.log ((η + 1 / 2) / (η + 1 / 2 - δ)) <
        2 * Real.log ((η + 1 / 2) / η) := by
    have hpos₁ : 0 < (η + 1 / 2) / (η + 1 / 2 - δ) :=
      div_pos hηhalf hd
    have hpos₂ : 0 < (η + 1 / 2) / η :=
      div_pos hηhalf hη
    have hrecip :
        (η + 1 / 2) / (η + 1 / 2 - δ) < (η + 1 / 2) / η := by
      apply (div_lt_div_iff₀ hd hη).2
      nlinarith
    exact (mul_lt_mul_of_pos_left
      (Real.strictMonoOn_log hpos₁ hpos₂ hrecip) (by norm_num))
  have heq :
      (η + 1 / 2) / η = 1 + 1 / (2 * η) := by
    field_simp [ne_of_gt hη]
  have hsmall : 0 < 1 / (2 * η) := by positivity
  have hlog_upper :
      Real.log (1 + 1 / (2 * η)) < 1 / (2 * η) := by
    have hlog := Real.log_lt_sub_one_of_pos
      (x := 1 + 1 / (2 * η)) (by linarith) (by linarith)
    nlinarith
  have hreciprocal : (1 / η : ℝ) = 2 * (1 / (2 * η)) := by
    field_simp [ne_of_gt hη]
  have hlast :
      2 * Real.log (1 + 1 / (2 * η)) < 1 / η := by
    rw [hreciprocal]
    nlinarith
  exact ⟨hfirst, by rw [heq], hlast⟩

/-- Claim 42871: derivative of the cosine factor at a positive odd center. -/
theorem cosineFactor_deriv_at_positiveOdd_claim42871 (n : ℕ) :
    deriv (fun s : ℝ => Real.cos (Real.pi * s / 2)) (2 * (n : ℝ) + 1) =
      -Real.sin (Real.pi * (2 * (n : ℝ) + 1) / 2) * (Real.pi / 2) := by
  have hinner : HasDerivAt (fun s : ℝ => Real.pi * s / 2)
      (Real.pi / 2) (2 * (n : ℝ) + 1) := by
    have h := hasDerivAt_const_mul (Real.pi / 2)
      (x := 2 * (n : ℝ) + 1)
    convert h using 1
    · ext s
      ring_nf
    · ring_nf
  have hcomp :=
    (Real.hasDerivAt_cos (Real.pi * (2 * (n : ℝ) + 1) / 2)).comp
      (2 * (n : ℝ) + 1) hinner
  have hderiv : HasDerivAt (fun s : ℝ => Real.cos (Real.pi * s / 2))
      (-Real.sin (Real.pi * (2 * (n : ℝ) + 1) / 2) * (Real.pi / 2))
      (2 * (n : ℝ) + 1) := by
    convert hcomp using 1 <;> rfl
  exact hderiv.deriv

/-- Claim 19365: the exact outer-product expansion for a two-atom vector. -/
theorem twoAtomOuterProductExpansion_claim19365
    {n : ℕ} (w₁ w₂ : ℝ) (u v : Fin n → ℝ) :
    let m : Fin n → ℝ := w₁ • u + w₂ • v
    (fun i j => m i * m j) =
      (fun i j => w₁ ^ 2 * (u i * u j) +
        w₂ ^ 2 * (v i * v j) +
        w₁ * w₂ * (u i * v j + v i * u j)) := by
  dsimp
  funext i j
  ring

end MathlibPlus.Analysis.Claim15256_42871_11628_19365
