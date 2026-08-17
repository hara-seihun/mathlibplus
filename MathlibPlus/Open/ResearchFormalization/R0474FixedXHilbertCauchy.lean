import Mathlib

open Asymptotics Filter

namespace MathlibPlus.Open.ResearchFormalization.R0474

noncomputable section

/-- The parameter-two generalized Laguerre polynomial on the complex plane. -/
def generalizedLaguerreTwoComplex (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ k * (Nat.choose (n + 2) (n - k) : ℂ) * z ^ k /
      (Nat.factorial k : ℂ)

/-- The zeroed first-shift Laguerre atom used by the feature. -/
def laguerreAtomComplex (n : ℕ) (z : ℂ) : ℂ :=
  if n < 2 then 0 else generalizedLaguerreTwoComplex (n - 2) z

/-- The Poisson weight in the fixed positive real parameter. -/
def poissonWeight_21850 (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

/-- The explicit complex first-shift feature coordinates. -/
def complexFeature_21850 (x : ℝ) (z : ℂ) (n : ℕ) : ℂ × ℂ :=
  let p : ℝ := poissonWeight_21850 x n
  (((Real.sqrt p : ℝ) : ℂ) * laguerreAtomComplex n z,
    ((Real.sqrt p : ℝ) : ℂ) * laguerreAtomComplex (n + 1) z)

/-- Membership in the concrete coordinate realization of the feature Hilbert
space. -/
def isFeatureVector_21850 (u : ℕ → ℂ × ℂ) : Prop :=
  Summable (fun n : ℕ =>
    (‖(u n).1‖ ^ 2 + ‖(u n).2‖ ^ 2))

/-- The Hilbert feature norm in the same coordinate realization. -/
def featureNorm_21850 (u : ℕ → ℂ × ℂ) : ℝ :=
  Real.sqrt (∑' n : ℕ,
    (‖(u n).1‖ ^ 2 + ‖(u n).2‖ ^ 2))

/-- The coordinatewise complex derivative of the feature at a real point. -/
def complexFeatureDerivative_21850 (x : ℝ) (m : ℕ) (t : ℝ) :
    ℕ → ℂ × ℂ :=
  fun n =>
    iteratedDeriv m (fun z : ℂ => complexFeature_21850 x z n) (t : ℂ)

/-- Claim 21850: for each fixed positive x and each fixed cubic-root
O(T^(2/3)) displacement constant, the unit-radius Hilbert Cauchy derivative
bound has the stated m! factor and fixed-x error scale. -/
def claim21850_fixedXHilbertCauchyDerivativeBound : Prop :=
  ∀ x : ℝ, 0 < x →
    ∀ A : ℝ, 0 ≤ A →
      ∃ E : ℝ → ℝ,
        IsBigO atTop E
            (fun T : ℝ => Real.rpow T (1 / 3 : ℝ) + Real.log T) ∧
          ∀ᶠ T : ℝ in atTop,
            ∀ t : ℝ,
              |t - T| ≤ A * Real.rpow T (2 / 3 : ℝ) →
                ∀ m : ℕ,
                  isFeatureVector_21850
                      (complexFeatureDerivative_21850 x m t) ∧
                    featureNorm_21850
                        (complexFeatureDerivative_21850 x m t) ≤
                      (Nat.factorial m : ℝ) *
                        Real.exp
                          ((3 / 2 : ℝ) * Real.rpow x (1 / 3 : ℝ) *
                              Real.rpow T (2 / 3 : ℝ) + E T)

end

end MathlibPlus.Open.ResearchFormalization.R0474
