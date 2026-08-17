import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R3803.Claim51633

open MathlibPlus.Open.OracleAreaOccupation
open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

/-- The one-atom law used for a constant insertion. -/
def diracLaw51633 {n : ℕ} (c : Driver n) : BooleanLaw n :=
  [(c, 1)]

/-- The law `t δ_c + (1 - t) ν` in the finite-list Boolean-law carrier. -/
def constantBlendLaw51633 {n : ℕ} (t : ℝ)
    (c : Driver n) (nu : BooleanLaw n) : BooleanLaw n :=
  (diracLaw51633 c).map (fun entry => (entry.1, t * entry.2)) ++
    nu.map (fun entry => (entry.1, (1 - t) * entry.2))

/-- The point `t c + (1 - t) E_ν K` on the configuration cube. -/
def constantBlendPoint51633 {n : ℕ} (t : ℝ)
    (c : Driver n) (nu : BooleanLaw n) : Configuration n → ℝ :=
  fun ω => t * driverValue c ω + (1 - t) * lawBarycentre nu ω

/-- The defect expectation `B(λ) = E_λ[e_H(E_λ H)]`. -/
noncomputable def radialB51633 {n : ℕ} (law : BooleanLaw n) : ℝ :=
  lawExpectation law (fun H => defect H (lawBarycentre law))

/-- The expected query cost and constrained area at a fixed barycentre. -/
noncomputable def expectedQ51633 {n : ℕ} (law : BooleanLaw n) : ℝ :=
  lawExpectation law qCost

noncomputable def expectedF51633 {n : ℕ} (law : BooleanLaw n)
    (u : Configuration n → ℝ) : ℝ :=
  lawExpectation law (fun K => constrainedValue K u)

/-- The constant-target area `A(u)`. -/
noncomputable def constantTargetArea51633 {n : ℕ}
    (c : Driver n) (u : Configuration n → ℝ) : ℝ :=
  constrainedValue c u

/-- A driver is a constant Boolean atom. -/
def constantDriver51633 {n : ℕ} (c : Driver n) : Prop :=
  ∃ s : Sign, ∀ ω : Configuration n, c ω = s

/-- The two translation-invariance and quadratic-homogeneity identities in the
constant-insertion argument. -/
noncomputable def constantInsertionScaling51633 {n : ℕ}
    (t : ℝ) (c : Driver n) (nu : BooleanLaw n) : Prop :=
  let beta := 1 - t
  let v := lawBarycentre nu
  let u := constantBlendPoint51633 t c nu
  constantTargetArea51633 c u = beta ^ 2 * constantTargetArea51633 c v ∧
    ∀ K : Driver n, constrainedValue K u = beta ^ 2 * constrainedValue K v

/-- Claim 51633: constant insertion has the exact radial-defect identity and
nonpositive sign, with the stated scaling of the constant-target and
constrained values. -/
def claim51633 : Prop :=
  ∀ (n : ℕ) (c : Driver n) (nu : BooleanLaw n) (t : ℝ),
    constantDriver51633 c →
    isProbabilityLaw nu →
    0 ≤ t →
    t ≤ 1 →
    constantInsertionScaling51633 t c nu ∧
      let beta := 1 - t
      let v := lawBarycentre nu
      radialB51633 (constantBlendLaw51633 t c nu) -
          beta ^ 2 * radialB51633 nu =
        -t * beta *
          (expectedQ51633 nu + beta *
            (expectedF51633 nu v - constantTargetArea51633 c v)) ∧
      radialB51633 (constantBlendLaw51633 t c nu) -
          beta ^ 2 * radialB51633 nu ≤ 0

end MathlibPlus.Open.ResearchFormalization.R3803.Claim51633
