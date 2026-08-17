import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

namespace MathlibPlus.Open.ResearchFormalization.R3803.Claim51638

open scoped BigOperators
open MathlibPlus.Open.OracleAreaOccupation
open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

noncomputable section

private def diracLaw51638 {n : ℕ} (h : Driver n) : BooleanLaw n :=
  [(h, 1)]

private def endpointLaw51638 {n : ℕ} (epsilon : ℝ)
    (h : Driver n) (mu : BooleanLaw n) : BooleanLaw n :=
  (diracLaw51638 h).map (fun entry =>
    (entry.1, (1 - epsilon) * entry.2)) ++
    mu.map (fun entry => (entry.1, epsilon * entry.2))

private def constantBlendLaw51638 {n : ℕ} (t : ℝ)
    (c : Driver n) (mu : BooleanLaw n) : BooleanLaw n :=
  (diracLaw51638 c).map (fun entry => (entry.1, t * entry.2)) ++
    mu.map (fun entry => (entry.1, (1 - t) * entry.2))

private def endpointDirection51638 {n : ℕ} (mu : BooleanLaw n)
    (h : Driver n) : Configuration n → ℝ :=
  fun ω => lawBarycentre mu ω - driverValue h ω

private def lexLE51638 (a b : ℝ × (ℝ × ℝ)) : Prop :=
  a.1 < b.1 ∨
    (a.1 = b.1 ∧
      (a.2.1 < b.2.1 ∨
        (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2)))

private def lexSelected51638 {n : ℕ}
    (K h : Driver n) (d : Configuration n → ℝ)
    (p : DeterministicPolicy n) : Prop :=
  qOptimal K p ∧
    ∀ p' : DeterministicPolicy n,
      qOptimal K p' →
        lexLE51638
          (policyArea p (driverValue h),
            (policyBilinear p (driverValue h) d, policyArea p d))
          (policyArea p' (driverValue h),
            (policyBilinear p' (driverValue h) d, policyArea p' d))

private def selectionFamily51638 {n : ℕ}
    (h : Driver n) (d : Configuration n → ℝ)
    (pick : Driver n → DeterministicPolicy n) : Prop :=
  ∀ K : Driver n, lexSelected51638 K h d (pick K)

private def nonconstantDriver51638 {n : ℕ} (h : Driver n) : Prop :=
  ∃ ω ω' : Configuration n, driverValue h ω ≠ driverValue h ω'

private def constantDriver51638 {n : ℕ} (h : Driver n) : Prop :=
  ∃ s : Sign, ∀ ω : Configuration n, h ω = s

private def lawMass51638 {n : ℕ} (mu : BooleanLaw n)
    (K : Driver n) : ℝ :=
  (mu.map (fun entry =>
    @ite ℝ (entry.1 = K) (Classical.propDecidable _) entry.2 0)).sum

private def lawIsDirac51638 {n : ℕ} (mu : BooleanLaw n)
    (h : Driver n) : Prop :=
  ∀ K : Driver n,
    lawMass51638 mu K =
      @ite ℝ (K = h) (Classical.propDecidable _) 1 0

private def offMass51638 {n : ℕ} (mu : BooleanLaw n)
    (h : Driver n) : ℝ :=
  (mu.map (fun entry =>
    @ite ℝ (entry.1 ≠ h) (Classical.propDecidable _) entry.2 0)).sum

private noncomputable def endpointA51638 {n : ℕ}
    (h : Driver n) (mu : BooleanLaw n)
    (pick : Driver n → DeterministicPolicy n) : ℝ :=
  let d := endpointDirection51638 mu h
  2 * policyBilinear (pick h) (driverValue h) d +
    lawExpectation mu (fun K => defect K (driverValue h))

private noncomputable def endpointC51638 {n : ℕ}
    (h : Driver n) (mu : BooleanLaw n)
    (pick : Driver n → DeterministicPolicy n) : ℝ :=
  let d := endpointDirection51638 mu h
  policyArea (pick h) d -
    lawExpectation mu (fun K => policyArea (pick K) d)

private noncomputable def endpointCharge51638 {n : ℕ}
    (h : Driver n) (rho : DeterministicPolicy n)
    (K : Driver n) : ℝ :=
  2 * policyBilinear rho (driverValue h)
      (fun ω => driverValue K ω - driverValue h ω) +
    defect K (driverValue h)

private noncomputable def radialB51638 {n : ℕ}
    (law : BooleanLaw n) : ℝ :=
  lawExpectation law (fun H => defect H (lawBarycentre law))

private noncomputable def expectedQ51638 {n : ℕ}
    (law : BooleanLaw n) : ℝ :=
  lawExpectation law qCost

private noncomputable def expectedF51638 {n : ℕ}
    (law : BooleanLaw n) (u : Configuration n → ℝ) : ℝ :=
  lawExpectation law (fun K => constrainedValue K u)

private noncomputable def constantTargetArea51638 {n : ℕ}
    (c : Driver n) (u : Configuration n → ℝ) : ℝ :=
  constrainedValue c u

private noncomputable def constantInsertionIdentity51638 {n : ℕ}
    (c : Driver n) (mu : BooleanLaw n) (t : ℝ) : Prop :=
  let beta := 1 - t
  let v := lawBarycentre mu
  radialB51638 (constantBlendLaw51638 t c mu) -
      beta ^ 2 * radialB51638 mu =
    -t * beta *
      (expectedQ51638 mu + beta *
        (expectedF51638 mu v - constantTargetArea51638 c v)) ∧
    radialB51638 (constantBlendLaw51638 t c mu) -
        beta ^ 2 * radialB51638 mu ≤ 0

private noncomputable def endpointScore51638 {n : ℕ}
    (h : Driver n) : ℝ :=
  score (diracLaw51638 h) h

/-- Claim 51638: at a nonconstant Boolean endpoint, the correctly oriented
perturbation `(1-epsilon) delta_h + epsilon mu`, with policies selected by the
stated lexicographic triple, has the cubic local score expansion and strict
stability away from the endpoint; constant endpoints retain the non-strict
contraction identity. -/
def claim51638 : Prop :=
  ∀ (n : ℕ) (h : Driver n),
    nonconstantDriver51638 h →
    ∀ (mu : BooleanLaw n), isProbabilityLaw mu →
      let d := endpointDirection51638 mu h
      ∀ (pick : Driver n → DeterministicPolicy n),
        selectionFamily51638 h d pick →
        (constrainedValue h (driverValue h) = qCost h →
          let A := endpointA51638 h mu pick
          let C := endpointC51638 h mu pick
          (∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
            ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon₀ →
              score (endpointLaw51638 epsilon h mu) h =
                epsilon * A + epsilon ^ 3 * C) ∧
          A ≤ 0 ∧
          (∀ K : Driver n, K ≠ h →
            endpointCharge51638 h (pick h) K < 0) ∧
          (offMass51638 mu h > 0 → A < 0) ∧
          (A = 0 →
            lawIsDirac51638 mu h ∧
              d = (fun _ => 0) ∧ C = 0) ∧
          (¬ lawIsDirac51638 mu h →
            ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
              ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon₀ →
                score (endpointLaw51638 epsilon h mu) h < 0)) ∧
        (constrainedValue h (driverValue h) < qCost h →
          endpointScore51638 h = 2 * defect h (driverValue h) ∧
            2 * defect h (driverValue h) < 0) ∧
        (∀ c : Driver n, constantDriver51638 c →
          ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            constantInsertionIdentity51638 c mu t)

end

end MathlibPlus.Open.ResearchFormalization.R3803.Claim51638
