import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The half-density event charge from Claim 14478, on its stated domain. -/
noncomputable def halfDensityEventCharge (U : {u : ℝ // 0 ≤ u}) : ℝ :=
  (Finset.sum (Finset.Icc 1 (Nat.floor (Real.exp (U : ℝ))))
      (fun n => (ArithmeticFunction.vonMangoldt n) / Real.sqrt (n : ℝ)))
    - 2 * (Real.exp ((U : ℝ) / 2) - 1)

/-- The predicate used here for a nontrivial zero of the Riemann zeta function. -/
def nontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The supremum in Claim 14483. -/
noncomputable def rightmostZeroDisplacement : ℝ :=
  sSup {x : ℝ | ∃ ρ : ℂ, nontrivialZetaZero ρ ∧ x = ρ.re - 1 / 2}

/-- The reflected atom and its imbalance from Claim 14497. -/
noncomputable def reflectedAdversarialAtomData
    (lam : {x : ℝ // x ≠ 0}) (r : {x : ℝ // 0 < x}) : (ℂ → ℂ) × ℝ :=
  (fun z : ℂ =>
      (1 + (r : ℂ) * Complex.exp ((lam : ℂ) * z)) *
        (1 + (r : ℂ) * Complex.exp (-((lam : ℂ) * z))),
    Real.log (r : ℝ) / (lam : ℝ))

/-- The zero-line assertion from Claim 14498. -/
def reflectedAdversarialAtomZeroLines : Prop :=
  ∀ (lam : {x : ℝ // 0 < x}) (r : {x : ℝ // 0 < x}),
    let atom :=
      reflectedAdversarialAtomData
        (⟨(lam : ℝ), ne_of_gt lam.property⟩ : {x : ℝ // x ≠ 0}) r
    let θ := atom.2
    (∀ z : ℂ, atom.1 z = 0 → z.re = θ ∨ z.re = -θ) ∧
      ((r : ℝ) = 1 ↔ θ = 0) ∧
      ((r : ℝ) = 1 → ∀ z : ℂ, atom.1 z = 0 → z.re = 0)

end MathlibPlus.Open.ResearchFormalizationBatch
