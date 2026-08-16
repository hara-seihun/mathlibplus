import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 11192: the specified piecewise-constant compact cosine transform has
explicit nonreal zeros. -/
def piecewiseConstantTransformWithNonrealZeros_claim11192 : Prop :=
  let h : ℝ → ℝ := fun x =>
    if x < 3 then (5 / 8 : ℝ) else if 3 < x then (-3 / 8 : ℝ) else 0
  let hderiv : ℝ → ℝ := fun x => deriv h x
  let F : ℂ → ℂ := fun z =>
    ∫ x in (0 : ℝ)..4,
      (h x : ℂ) * Complex.cos (z * ((x - 2 : ℝ) : ℂ))
  let smoothRemainder : ℂ → ℂ := fun z =>
    (∫ x in (0 : ℝ)..3,
      (hderiv x : ℂ) * Complex.sin (z * ((x - 2 : ℝ) : ℂ))) +
    (∫ x in (3 : ℝ)..4,
      (hderiv x : ℂ) * Complex.sin (z * ((x - 2 : ℝ) : ℂ)))
  (∀ z : ℂ,
      smoothRemainder z = 0 ∧
        z * F z = Complex.sin z + (1 / 4 : ℂ) * Complex.sin (2 * z) ∧
        z * F z = Complex.sin z * (1 + (1 / 2 : ℂ) * Complex.cos z)) ∧
    (∀ k : ℤ,
      let realPart : ℝ := ((2 * k + 1 : ℤ) : ℝ) * Real.pi
      let height : ℝ := Real.arcosh 2
      let zPlus : ℂ := (realPart : ℂ) + Complex.I * (height : ℂ)
      let zMinus : ℂ := (realPart : ℂ) - Complex.I * (height : ℂ)
      F zPlus = 0 ∧ zPlus.im ≠ 0 ∧
        F zMinus = 0 ∧ zMinus.im ≠ 0)

/-- Claim 11219: reflection-evenness of a finite canonical theta-shell block
forces every positive-integer shell moment to vanish. -/
def powerSumConsequencesOfReflectionEvenness_claim11219 : Prop :=
  ∀ (M : ℕ) (n : Fin M → ℕ) (a : Fin M → ℝ),
    (∀ j, 0 < n j) →
    (∀ i j, n i = n j → i = j) →
      let h : ℝ → ℝ := fun x => (4 * x ^ 2 - 6 * x) * Real.exp (-x)
      let phi : ℕ → ℝ → ℝ := fun label u =>
        Real.exp (u / 2) *
          h (Real.pi * (label : ℝ) ^ 2 * Real.exp (2 * u))
      let F : ℝ → ℝ := fun u => ∑ j, a j * phi (n j) u
      (∀ u, F u = F (-u)) →
        ∀ k : ℤ, 1 ≤ k →
          ∑ j, a j * ((n j : ℝ) ^ (2 * k)) = 0

/-- Claim 11222: consecutive shell moments have generalized Vandermonde
rigidity, including the stated consequence for finite reflected shell blocks. -/
def generalizedVandermondeRigidity_claim11222 : Prop :=
  ∀ (M : ℕ) (n : Fin M → ℕ) (a : Fin M → ℝ) (K : ℤ),
    1 ≤ K →
    (∀ j, 0 < n j) →
    (∀ i j, n i = n j → i = j) →
      let h : ℝ → ℝ := fun x => (4 * x ^ 2 - 6 * x) * Real.exp (-x)
      let phi : ℕ → ℝ → ℝ := fun label u =>
        Real.exp (u / 2) *
          h (Real.pi * (label : ℝ) ^ 2 * Real.exp (2 * u))
      let F : ℝ → ℝ := fun u => ∑ j, a j * phi (n j) u
      let momentCancellation : Prop :=
        ∀ r : Fin M,
          ∑ j, a j * ((n j : ℝ) ^ (2 * (K + (r : ℤ)))) = 0
      (momentCancellation → ∀ j, a j = 0) ∧
        ((∀ u, F u = F (-u)) →
          momentCancellation → ¬ (∃ j, a j ≠ 0))

/-- Claim 11228: the explicit positive reciprocal-amplitude counterfeit has
reflection symmetry and is strictly positive on the imaginary axis, while it
still has zeros off that axis. -/
def softReciprocalCriteriaDoNotLocalizeZeros_claim11228 : Prop :=
  let reciprocalAmplitude : ℂ → ℂ := fun z =>
    (5 : ℂ) +
      (2 : ℂ) *
        (Complex.exp (z * (Real.log 2 : ℂ)) +
          Complex.exp (-z * (Real.log 2 : ℂ)))
  let offAxisZero : ℂ :=
    (1 : ℂ) +
      (((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I)
  (∀ z : ℂ, reciprocalAmplitude z = reciprocalAmplitude (-z)) ∧
    (0 < (5 : ℝ) ∧ 0 < (2 : ℝ)) ∧
    (∀ t : ℝ,
      reciprocalAmplitude (Complex.I * (t : ℂ)) =
          ((5 + 4 * Real.cos (t * Real.log 2) : ℝ) : ℂ) ∧
        1 ≤ 5 + 4 * Real.cos (t * Real.log 2)) ∧
    reciprocalAmplitude offAxisZero = 0 ∧
      offAxisZero.re ≠ 0 ∧
      ¬ (∀ z : ℂ, reciprocalAmplitude z = 0 → z.re = 0)

end MathlibPlus.Open.Analysis
