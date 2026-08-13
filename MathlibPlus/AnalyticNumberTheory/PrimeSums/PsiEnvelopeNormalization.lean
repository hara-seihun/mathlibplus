import Batteries
import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.ChebyshevTailAndPsiEnvelope

namespace MathlibPlus.AnalyticNumberTheory.PrimeSums

open MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/-- The normalized and de-normalized global psi envelopes are the same bound. -/
theorem globalPsiNormalizedEnvelope_iff_exactPsiEnvelopeDenormalization :
    globalPsiNormalizedEnvelope ↔ exactPsiEnvelopeDenormalization := by
  let R : ℝ := 55666305 / 10000000
  let A : ℝ := 121096 / 1000
  let p : ℝ := 3 / 2
  let c : ℝ := A / R ^ p
  let d : ℝ := 2 / Real.sqrt R
  let cLower : ℝ := 92202183441759598 / 10000000000000000
  let cUpper : ℝ := 92202183441759599 / 10000000000000000
  let dLower : ℝ := 8476836336683192 / 10000000000000000
  let dUpper : ℝ := 8476836336683193 / 10000000000000000
  let dRounded : ℝ := 8476836 / 10000000
  let dMargin : ℝ := 33668 / 1000000000000
  have hR : 0 < R := by norm_num [R]
  have hsqrtR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hRpow : R ^ p = R * Real.sqrt R := by
    dsimp [p]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hdenom : 0 < R * Real.sqrt R := mul_pos hR hsqrtR
  have hcLower : cLower ≤ c := by
    dsimp [c]
    rw [hRpow]
    apply (le_div_iff₀ hdenom).2
    have hsquare :
        (cLower * (R * Real.sqrt R)) ^ 2 ≤ A ^ 2 := by
      calc
        (cLower * (R * Real.sqrt R)) ^ 2 =
            cLower ^ 2 * R ^ 2 * (Real.sqrt R) ^ 2 := by ring
        _ = cLower ^ 2 * R ^ 2 * R := by rw [Real.sq_sqrt hR.le]
        _ ≤ A ^ 2 := by norm_num [cLower, R, A]
    have hleft : 0 ≤ cLower * (R * Real.sqrt R) := by
      positivity
    have hA : 0 ≤ A := by norm_num [A]
    exact (sq_le_sq₀ hleft hA).mp hsquare
  have hcUpper : c < cUpper := by
    dsimp [c]
    rw [hRpow]
    apply (div_lt_iff₀ hdenom).2
    have hsquare :
        A ^ 2 < (cUpper * (R * Real.sqrt R)) ^ 2 := by
      calc
        A ^ 2 < cUpper ^ 2 * R ^ 2 * R := by
          norm_num [cUpper, R, A]
        _ = cUpper ^ 2 * R ^ 2 * (Real.sqrt R) ^ 2 := by
          rw [Real.sq_sqrt hR.le]
        _ = (cUpper * (R * Real.sqrt R)) ^ 2 := by ring
    have hright : 0 ≤ cUpper * (R * Real.sqrt R) := by
      positivity
    have hA : 0 ≤ A := by norm_num [A]
    exact (sq_lt_sq₀ hA hright).mp hsquare
  have hdLower : dLower ≤ d := by
    dsimp [d]
    apply (le_div_iff₀ hsqrtR).2
    have hsquare :
        (dLower * Real.sqrt R) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      calc
        (dLower * Real.sqrt R) ^ 2 =
            dLower ^ 2 * (Real.sqrt R) ^ 2 := by ring
        _ = dLower ^ 2 * R := by rw [Real.sq_sqrt hR.le]
        _ ≤ (2 : ℝ) ^ 2 := by norm_num [dLower, R]
    have hleft : 0 ≤ dLower * Real.sqrt R := by positivity
    exact (sq_le_sq₀ hleft (by norm_num)).mp hsquare
  have hdUpper : d < dUpper := by
    dsimp [d]
    apply (div_lt_iff₀ hsqrtR).2
    have hsquare :
        (2 : ℝ) ^ 2 < (dUpper * Real.sqrt R) ^ 2 := by
      calc
        (2 : ℝ) ^ 2 < dUpper ^ 2 * R := by norm_num [dUpper, R]
        _ = dUpper ^ 2 * (Real.sqrt R) ^ 2 := by
          rw [Real.sq_sqrt hR.le]
        _ = (dUpper * Real.sqrt R) ^ 2 := by ring
    have hright : 0 ≤ dUpper * Real.sqrt R := by positivity
    exact (sq_lt_sq₀ (by norm_num) hright).mp hsquare
  have hdMargin : d - dRounded > dMargin := by
    have : dLower - dRounded > dMargin := by
      norm_num [dLower, dRounded, dMargin]
    linarith
  have henvelope (x : ℝ) (hx : 2 < x) :
      A * (Real.log x / R) ^ p *
          Real.exp (-2 * Real.sqrt (Real.log x / R)) =
        c * (Real.log x) ^ p *
          Real.exp (-d * Real.sqrt (Real.log x)) := by
    have hlog : 0 ≤ Real.log x := (Real.log_pos (by linarith)).le
    dsimp [c, d]
    rw [Real.div_rpow hlog hR.le p, Real.sqrt_div hlog R]
    have hexp :
        -2 * (Real.sqrt (Real.log x) / Real.sqrt R) =
          -(2 / Real.sqrt R) * Real.sqrt (Real.log x) := by ring
    rw [hexp]
    ring
  change
    (∀ x : ℝ, 2 < x →
      |(Chebyshev.psi x - x) / x| ≤
        A * (Real.log x / R) ^ p *
          Real.exp (-2 * Real.sqrt (Real.log x / R))) ↔
      ((∀ x : ℝ, 2 < x →
        |(Chebyshev.psi x - x) / x| ≤
          c * (Real.log x) ^ p *
            Real.exp (-d * Real.sqrt (Real.log x))) ∧
        cLower ≤ c ∧ c < cUpper ∧ dLower ≤ d ∧ d < dUpper ∧
          d - dRounded > dMargin)
  constructor
  · intro h
    refine ⟨?_, hcLower, hcUpper, hdLower, hdUpper, hdMargin⟩
    intro x hx
    rw [← henvelope x hx]
    exact h x hx
  · rintro ⟨h, _⟩ x hx
    rw [henvelope x hx]
    exact h x hx

end MathlibPlus.AnalyticNumberTheory.PrimeSums
