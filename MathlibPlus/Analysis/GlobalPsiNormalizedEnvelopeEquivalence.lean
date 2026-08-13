import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.ChebyshevTailAndPsiEnvelope

namespace MathlibPlus.AnalyticNumberTheory.PrimeSums

noncomputable section

local notation "R0" => (55666305 / 10000000 : ℝ)
local notation "A0" => (121096 / 1000 : ℝ)
local notation "cL" => (92202183441759598 / 10000000000000000 : ℝ)
local notation "cU" => (92202183441759599 / 10000000000000000 : ℝ)
local notation "dL" => (8476836336683192 / 10000000000000000 : ℝ)
local notation "dU" => (8476836336683193 / 10000000000000000 : ℝ)
local notation "d0" => (8476836 / 10000000 : ℝ)
local notation "eps" => (33668 / 1000000000000 : ℝ)

private lemma hR : 0 < R0 := by norm_num
private lemma hA : 0 < A0 := by norm_num

private lemma hRpow : R0 ^ (3 / 2 : ℝ) = R0 * Real.sqrt R0 := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_add hR, Real.rpow_one, ← Real.sqrt_eq_rpow]

private lemma hR_sq : (Real.sqrt R0) ^ 2 = R0 :=
  Real.sq_sqrt (le_of_lt hR)

private lemma hRsqrt : 0 < Real.sqrt R0 := Real.sqrt_pos.2 hR

private lemma hC_lower_sq : (cL * R0) ^ 2 * R0 ≤ A0 ^ 2 := by
  norm_num

private lemma hC_upper_sq : A0 ^ 2 < (cU * R0) ^ 2 * R0 := by
  norm_num

private lemma hD_lower_sq : dL ^ 2 * R0 ≤ (2 : ℝ) ^ 2 := by
  norm_num

private lemma hD_upper_sq : (2 : ℝ) ^ 2 < dU ^ 2 * R0 := by
  norm_num

private lemma hmargin : d0 + eps < dL := by
  norm_num

private lemma hC_lower : cL ≤ A0 / R0 ^ (3 / 2 : ℝ) := by
  rw [hRpow]
  apply (le_div_iff₀ (mul_pos hR hRsqrt)).2
  have hs : (cL * R0 * Real.sqrt R0) ^ 2 ≤ A0 ^ 2 := by
    nlinarith [hC_lower_sq, hR_sq]
  have hnonneg : 0 ≤ cL * R0 * Real.sqrt R0 := by positivity
  simpa [mul_assoc] using (sq_le_sq₀ hnonneg (le_of_lt hA)).mp hs

private lemma hC_upper : A0 / R0 ^ (3 / 2 : ℝ) < cU := by
  rw [hRpow]
  apply (div_lt_iff₀ (mul_pos hR hRsqrt)).2
  have hs : A0 ^ 2 < (cU * R0 * Real.sqrt R0) ^ 2 := by
    nlinarith [hC_upper_sq, hR_sq]
  have hnonneg : 0 ≤ cU * R0 * Real.sqrt R0 := by positivity
  simpa [mul_assoc] using (sq_lt_sq₀ (le_of_lt hA) hnonneg).mp hs

private lemma hD_lower : dL ≤ 2 / Real.sqrt R0 := by
  apply (le_div_iff₀ hRsqrt).2
  have hs : (dL * Real.sqrt R0) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    nlinarith [hD_lower_sq, hR_sq]
  have hnonneg : 0 ≤ dL * Real.sqrt R0 := by positivity
  exact (sq_le_sq₀ hnonneg (by norm_num)).mp hs

private lemma hD_upper : 2 / Real.sqrt R0 < dU := by
  apply (div_lt_iff₀ hRsqrt).2
  have hs : (2 : ℝ) ^ 2 < (dU * Real.sqrt R0) ^ 2 := by
    nlinarith [hD_upper_sq, hR_sq]
  have hnonneg : 0 ≤ dU * Real.sqrt R0 := by positivity
  exact (sq_lt_sq₀ (by norm_num) hnonneg).mp hs

private lemma hD_margin : d0 + eps < 2 / Real.sqrt R0 :=
  lt_of_lt_of_le hmargin hD_lower

private lemma hEnvelope_eq (x : ℝ) (hx : 2 < x) :
    A0 * (Real.log x / R0) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (Real.log x / R0)) =
      (A0 / R0 ^ (3 / 2 : ℝ)) * (Real.log x) ^ (3 / 2 : ℝ) *
        Real.exp (-(2 / Real.sqrt R0) * Real.sqrt (Real.log x)) := by
  have hlog : 0 ≤ Real.log x := le_of_lt (Real.log_pos (by linarith))
  rw [Real.div_rpow hlog (le_of_lt hR) (3 / 2 : ℝ)]
  rw [Real.sqrt_div hlog]
  have hsqrt : Real.sqrt R0 ≠ 0 := ne_of_gt hRsqrt
  have hrpow : Real.rpow R0 (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hR _)
  have hexp : -2 * (Real.sqrt (Real.log x) / Real.sqrt R0) =
      -(2 / Real.sqrt R0) * Real.sqrt (Real.log x) := by
    field_simp
  rw [hexp]
  field_simp

/-- The normalized and de-normalized global psi envelopes are equivalent. -/
theorem globalPsiNormalizedEnvelope_iff_exactPsiEnvelopeDenormalization :
    MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.globalPsiNormalizedEnvelope ↔
      MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.exactPsiEnvelopeDenormalization := by
  dsimp [MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.globalPsiNormalizedEnvelope,
    MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.exactPsiEnvelopeDenormalization]
  constructor
  · intro h
    refine ⟨?_, hC_lower, hC_upper, hD_lower, hD_upper, ?_⟩
    · intro x hx
      rw [← hEnvelope_eq x hx]
      exact h x hx
    · linarith [hD_margin]
  · intro h x hx
    rw [hEnvelope_eq x hx]
    exact h.1 x hx

end
end MathlibPlus.AnalyticNumberTheory.PrimeSums
