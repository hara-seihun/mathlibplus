import Mathlib

/-!
# Completed-zeta Loewner positivity through order five

Registry statement for admitted claim 213.  The completed source and all
quantifiers are expanded locally so that the node does not depend on a
not-yet-admitted helper definition.
-/

namespace MathlibPlus.Open.Analysis.CompletedZeta

/-- The completed-zeta order-five positivity claim, including its finite-node
consequence, first-failure lower bound, and the three certified coverage
ranges used by the source. -/
noncomputable def globalOrderFivePositivity : Prop :=
  let xi : ℝ → ℝ := fun s =>
    (((1 / 2 : ℂ) * (s : ℂ) * ((s : ℂ) - 1) *
      completedRiemannZeta (s : ℂ))).re
  let logarithmicDerivative : ℝ → ℝ := fun r => deriv xi r / xi r
  let H : ℝ → ℝ := fun x => logarithmicDerivative (Real.sqrt x) / Real.sqrt x
  let C : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ := fun n x i j =>
    (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ) + 1) *
      iteratedDeriv ((i : ℕ) + (j : ℕ) + 1) H x /
        (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ)
  let dividedDifference : ℝ → ℝ → ℝ := fun x y =>
    if x = y then deriv H x else (H x - H y) / (x - y)
  let negativeLoewner : (n : ℕ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun n x i j => -dividedDifference (x i) (x j)
  let HasFailure : ℕ → Prop := fun n =>
    ∃ x : Fin n → ℝ,
      (∀ i, (1 : ℝ) / 4 < x i) ∧ ¬Matrix.PosSemidef (negativeLoewner n x)
  let IsFirstFailure : ℕ → Prop := fun n =>
    HasFailure n ∧ ∀ m < n, ¬HasFailure m
  (∀ x : ℝ, (1 : ℝ) / 4 < x → Matrix.PosDef (C 5 x)) ∧
  (∀ x : Fin 5 → ℝ,
    (∀ i, (1 : ℝ) / 4 < x i) → Matrix.PosSemidef (negativeLoewner 5 x)) ∧
  (∀ n : ℕ, IsFirstFailure n → 6 ≤ n) ∧
  (∀ x : ℝ, x ∈ Set.Icc ((1 : ℝ) / 4) 1260 → Matrix.PosDef (C 5 x)) ∧
  (∀ r : ℝ, r ∈ Set.Icc ((3549 : ℝ) / 100) 100 → Matrix.PosDef (C 5 (r ^ 2))) ∧
  (∀ r : ℝ, 100 ≤ r → Matrix.PosDef (C 5 (r ^ 2)))

/-- RH is equivalent to positive semidefiniteness of every finite Riemann
vertical-shift boundary-flux matrix for every `0 < ω < 1/2`. -/
noncomputable def riemannBoundaryFluxCriterion : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s
  let A : ℝ → ℝ → ℂ := fun ω q =>
    xi (((1 : ℝ) / 2 - ω : ℝ) + (q : ℂ) * Complex.I)
  let parameterDerivative : ℝ → ℝ → ℂ := fun ω q =>
    deriv (fun η : ℝ => A η q) ω
  let coordinateDerivative : ℝ → ℝ → ℂ := fun ω q =>
    deriv (A ω) q
  let mixedDerivative : ℝ → ℝ → ℂ := fun ω q =>
    deriv (parameterDerivative ω) q
  let boundaryFlux : ℝ → ℝ → ℝ → ℝ := fun ω p q =>
    if p = q then
      -(1 : ℝ) / 4 *
        ((mixedDerivative ω p * starRingEnd ℂ (A ω p)).im -
          (parameterDerivative ω p * starRingEnd ℂ (coordinateDerivative ω p)).im)
    else
      ((parameterDerivative ω q * starRingEnd ℂ (A ω p)).im -
          (parameterDerivative ω p * starRingEnd ℂ (A ω q)).im) /
        (4 * (p - q))
  RiemannHypothesis ↔
    ∀ ω : ℝ, 0 < ω → ω < (1 : ℝ) / 2 →
      ∀ n : ℕ, ∀ p : Fin n → ℝ, Function.Injective p →
        Matrix.PosSemidef (fun i j => boundaryFlux ω (p i) (p j))

end MathlibPlus.Open.Analysis.CompletedZeta
