import Mathlib

open scoped BigOperators Interval
open MeasureTheory Set Filter

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The prime-by-prime oscillatory series in the admitted finite-prime-tower claim. -/
def primeTowerTerm (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : {k : ℕ // 1 ≤ k},
    ((Real.log (p : ℝ) / Real.rpow (p : ℝ) ((k.1 : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp
        (-Complex.I * (k.1 : ℂ) * (t : ℂ) * (Real.log (p : ℝ) : ℂ))

/-- The sum of the prime-by-prime terms over a finite set of primes. -/
def primeTowerSum (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, primeTowerTerm p t

/-- The maximal-phase value from the admitted claim. -/
def primeTowerM (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1)

/-- The Lipschitz constant appearing in the return-density bound. -/
def primeTowerL (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Real.sqrt (p : ℝ) * Real.log (p : ℝ) /
    (Real.sqrt (p : ℝ) - 1) ^ 2

/-- The phase-space value indexed by the primes in `P`. -/
def primeTowerPhaseSum (P : Finset ℕ)
    (θ : {p : ℕ // p ∈ P} → ℝ) : ℂ :=
  ∑ p : {p : ℕ // p ∈ P},
    ((Real.log (p.1 : ℝ) : ℂ) /
      ((Real.sqrt (p.1 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (θ p : ℂ)) - 1))

/--
The admitted finite-prime-tower Haar equidistribution and coherent-return claim.
This is an open mathematical statement: no proof is supplied here.
-/
def finitePrimeTowerHaarCoherentDensity : Prop :=
  ∀ (P : Finset ℕ),
    P.Nonempty →
    (∀ p ∈ P, Nat.Prime p) →
    let m : ℕ := P.card
    let M_P : ℝ := primeTowerM P
    let L_P : ℝ := primeTowerL P
    (∀ (Φ : ℂ → ℂ), Continuous Φ →
      Tendsto
        (fun T : ℝ =>
          (1 / T) *
            ∫ t in (0 : ℝ)..T, Φ (primeTowerSum P t))
        atTop
        (nhds
          (((1 / ((2 * Real.pi) ^ m) : ℝ) : ℂ) *
            ∫ θ in Set.pi Set.univ (fun _ => Set.Icc (-Real.pi) Real.pi),
              Φ (primeTowerPhaseSum P θ)))) ∧
    (∀ ε : ℝ, 0 < ε → ε < Real.pi * L_P →
      Filter.liminf
          (fun T : ℝ =>
            (1 / T) *
              ENNReal.toReal
                (volume
                  {t : ℝ |
                    t ∈ Set.Icc (0 : ℝ) T ∧
                      ‖primeTowerSum P t - (M_P : ℂ)‖ < ε}))
          atTop ≥
        (ε / (Real.pi * L_P)) ^ m ∧
      0 < (ε / (Real.pi * L_P)) ^ m)

end
end MathlibPlus.Open.Analysis
