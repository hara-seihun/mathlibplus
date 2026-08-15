import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable def tauPrimePower (x : ℝ) (p r : ℕ) : ℂ :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    Complex.exp
      (Complex.I *
        ((((r : ℤ) - 2 * (j : ℤ) : ℤ) : ℂ) *
          ((x * Real.log (p : ℝ) : ℝ) : ℂ))))

noncomputable def primePowNeg (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * ((Real.log (p : ℝ) : ℝ) : ℂ))

noncomputable def thetaAtPrime (x : ℝ) (p : ℕ) : ℝ :=
  x * Real.log (p : ℝ)

def polarizedLocalEulerFactor : Prop :=
  ∀ (p : ℕ) (x y : ℝ) (s : ℂ),
    p.Prime →
    0 < s.re →
      let t := primePowNeg p s
      let θx := thetaAtPrime x p
      let θy := thetaAtPrime y p
      (∑' r : ℕ, tauPrimePower x p r * tauPrimePower y p r * t ^ r) =
        ((1 : ℂ) - t ^ 2) /
          Finset.prod ({-1, 1} : Finset ℤ) (fun ε =>
            Finset.prod ({-1, 1} : Finset ℤ) (fun δ =>
              (1 : ℂ) -
                Complex.exp
                  (Complex.I *
                    (((ε : ℂ) * (θx : ℂ)) + ((δ : ℂ) * (θy : ℂ)))) * t))

end MathlibPlus.Open.Analysis
