import MathlibPlus.Open.Analysis.Claim3381

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim3391

open MathlibPlus.Open.Analysis.Claim3381

noncomputable def thetaShell (q : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-Real.pi * (q : ℝ) ^ 2 * Real.exp (2 * u))

noncomputable def thetaShellMomentIntegrand (q : ℕ) (x u : ℝ) : ℝ :=
  Real.exp (u / 2) * thetaShell q u * Real.rpow u (2 * x)

/-- The exact first-shell phase saddle used to define the moving window. -/
def thetaSaddleEquation (x u : ℝ) : Prop :=
  0 < u ∧
    2 * x / u + (1 : ℝ) / 2 =
      2 * Real.pi * Real.exp (2 * u)

/-- A point satisfying the phase equation and its uniqueness. -/
def uniqueThetaSaddle (x ux : ℝ) : Prop :=
  thetaSaddleEquation x ux ∧
    ∀ v : ℝ, thetaSaddleEquation x v → v = ux

/-- The window of width sqrt(u_x/x) log x around the first-shell saddle. -/
def thetaSaddleWindow (x ux u : ℝ) : Prop :=
  0 < u ∧ |u - ux| ≤ Real.sqrt (ux / x) * Real.log x

noncomputable def lambertScale (x : ℝ) : ℝ :=
  lambertW₀ (2 * x / Real.pi)

/--
Higher integer-square theta shells are compared with the *first* shell, not
with themselves.  The derivative quantifier is over the real moment parameter
x, so it records the fixed-parameter-derivative part of the claim.
-/
def higherThetaShellExponentialSeparation : Prop :=
  ∀ j : ℕ, ∃ c C X : ℝ,
    0 < c ∧ 0 < C ∧ 0 < X ∧
      ∀ x : ℝ, X ≤ x →
        0 < lambertScale x ∧
        ∃ ux : ℝ, uniqueThetaSaddle x ux ∧
          ∀ q : ℕ, 2 ≤ q →
            ∀ u : ℝ, thetaSaddleWindow x ux u →
              |iteratedDeriv j
                  (fun z : ℝ => thetaShellMomentIntegrand q z u) x| ≤
                C * Real.exp (-c * x / lambertScale x) *
                  thetaShellMomentIntegrand 1 x u

end MathlibPlus.Open.Analysis.Claim3391
