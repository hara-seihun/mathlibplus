import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0504Claims26023_26024

private abbrev Eight := Fin 8
private abbrev SexticCoefficients := Fin 4 → ℚ

private def reflectiveOn (N : ℕ) (l : ℕ → ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N → l t = l (N - t)

private def foldedFourIndex (N s : ℕ) : ℕ :=
  min s (N - s)

private def fourBlock (N : ℕ) (l : ℕ → ℚ) (μ : Eight → ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powerset.filter
      (fun S => S.card = 4),
    l (foldedFourIndex N (∑ i ∈ S, μ i))

private def eightFactorEquation
    (N : ℕ) (f h k l : ℕ → ℚ) (μ : Eight → ℕ) : ℚ :=
  (∑ i : Eight, f (μ i)) +
    (∑ i : Eight, ∑ j ∈ Finset.Ioi i, h (μ i + μ j)) +
    (∑ i : Eight, ∑ j ∈ Finset.Ioi i,
      ∑ r ∈ Finset.Ioi j, k (μ i + μ j + μ r)) +
    fourBlock N l μ

private def eightFactorAnnihilator
    (N : ℕ) (f h k l : ℕ → ℚ) : Prop :=
  reflectiveOn N l ∧
    ∀ μ : Eight → ℕ,
      (∑ i : Eight, μ i) = N →
        eightFactorEquation N f h k l μ = 0

private def sexticValue
    (N : ℕ) (d : SexticCoefficients) (t : ℕ) : ℚ :=
  let z : ℚ := (t : ℚ) * (N - t : ℕ)
  d 0 + d 1 * z + d 2 * z ^ 2 + d 3 * z ^ 3

private def polynomialValue (p : Polynomial ℚ) (t : ℕ) : ℚ :=
  p.eval (t : ℚ)

private structure EightParameters where
  d : SexticCoefficients
  p5 : Polynomial ℚ
  p3 : Polynomial ℚ
  B : ℚ
  A : ℚ

private def parameterL (N : ℕ) (p : EightParameters) (t : ℕ) : ℚ :=
  sexticValue N p.d t

private def parameterK (N : ℕ) (p : EightParameters) (t : ℕ) : ℚ :=
  polynomialValue p.p5 t - 2 * parameterL N p t

private def parameterH (N : ℕ) (p : EightParameters) (t : ℕ) : ℚ :=
  polynomialValue p.p3 t - 3 * parameterK N p t -
    parameterK N p (N - t) - 6 * parameterL N p t

private def parameterF (N : ℕ) (p : EightParameters) (t : ℕ) : ℚ :=
  p.A + p.B * (t : ℚ) - 5 * parameterH N p t -
    parameterH N p (N - t) - 10 * parameterK N p t -
    5 * parameterK N p (N - t) - 20 * parameterL N p t

private def endpointEquation (N : ℕ) (p : EightParameters) : Prop :=
  8 * p.A + p.B * (N : ℚ) =
    5 * parameterH N p N + 15 * parameterH N p 0 +
      24 * parameterK N p N + 40 * parameterK N p 0 +
        90 * parameterL N p 0

private def isDisplayedParameterization
    (N : ℕ) (f h k l : ℕ → ℚ) (p : EightParameters) : Prop :=
  p.p5.natDegree ≤ 5 ∧
    p.p3.natDegree ≤ 3 ∧
    endpointEquation N p ∧
    ∀ t : ℕ, t ≤ N →
      l t = parameterL N p t ∧
        k t = parameterK N p t ∧
          h t = parameterH N p t ∧
            f t = parameterF N p t

/-- Claim 26023: on the folded self-reciprocal four-sum carrier, every
    eight-factor annihilator has the unique sextic/quintic/cubic/affine
    parameterization and the displayed endpoint equation. -/
def claim26023_completeEightFactorAnnihilatorParameterization : Prop :=
  ∀ (N : ℕ) (f h k l : ℕ → ℚ),
    8 ≤ N →
      eightFactorAnnihilator N f h k l →
        ∃! p : EightParameters,
          isDisplayedParameterization N f h k l p

/-- Claim 26024: every choice of the displayed four sextic coefficients, a
    degree-at-most-five `p₅`, a degree-at-most-three `p₃`, and a slope gives a
    genuine annihilator whenever `A` satisfies the scalar endpoint equation.
    The annihilator predicate retains the folded reflection condition. -/
def claim26024_everyDisplayedFunctionalIsAnnihilator : Prop :=
  ∀ (N : ℕ) (d : SexticCoefficients)
    (p5 p3 : Polynomial ℚ) (B A : ℚ),
    8 ≤ N →
      p5.natDegree ≤ 5 →
        p3.natDegree ≤ 3 →
          let p : EightParameters :=
            { d := d, p5 := p5, p3 := p3, B := B, A := A }
          endpointEquation N p →
            eightFactorAnnihilator N
              (parameterF N p) (parameterH N p)
              (parameterK N p) (parameterL N p)

end MathlibPlus.Open.ResearchFormalization.BatchR0504Claims26023_26024
