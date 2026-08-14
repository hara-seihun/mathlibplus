import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0192

/-- Claim 18682.  The operator `D` and the kernel `K` are explicit source
carriers; the declaration records the three normalized iterates without
silently replacing them by a different operator. -/
def claim18682_normalizedLogDerivativeCurve
    (K : ℝ → ℝ → ℝ)
    (D : (ℝ → ℝ) → ℝ → ℝ)
    (gamma : ℝ → ℝ × ℝ × ℝ)
    (l : ℝ) : Prop :=
  ∀ q : ℝ,
    gamma q =
      (D (fun x => K x l) q / K q l,
       D (D (fun x => K x l)) q / K q l,
       D (D (D (fun x => K x l))) q / K q l)

/-- Claim 18683.  The q-derivatives are written with Mathlib's derivative
operator, while the two-variable source functions remain parameters. -/
def claim18683_gaussCurve
    (f g h : ℝ → ℝ → ℝ)
    (Gamma : ℝ → ℝ → ℝ × ℝ)
    (l : ℝ) : Prop :=
  ∀ q : ℝ,
    Gamma q l =
      (deriv (fun x => g x l) q / deriv (fun x => f x l) q,
       deriv (fun x => h x l) q / deriv (fun x => f x l) q)

/-- Claim 18684.  The three intervals, masses, and weighted barycenters are
written on the displayed four-knot carrier. -/
def claim18684_gapMassesAndWeightedBarycenters
    (f : ℝ → ℝ → ℝ)
    (Gamma : ℝ → ℝ → ℝ × ℝ)
    (l : ℝ)
    (q1 q2 q3 q4 : ℝ)
    (barGamma : Fin 3 → ℝ × ℝ) : Prop :=
  q1 < q2 ∧ q2 < q3 ∧ q3 < q4 ∧
    let fAtL : ℝ → ℝ := fun q => f q l
    let mass1 : ℝ := f q2 l - f q1 l
    let mass2 : ℝ := f q3 l - f q2 l
    let mass3 : ℝ := f q4 l - f q3 l
    let interval1 : Set ℝ := Set.Icc q1 q2
    let interval2 : Set ℝ := Set.Icc q2 q3
    let interval3 : Set ℝ := Set.Icc q3 q4
    mass1 > 0 ∧ mass2 > 0 ∧ mass3 > 0 ∧
      barGamma 0 =
        mass1⁻¹ • ∫ q in interval1, (deriv fAtL q) • Gamma q l ∂volume ∧
      barGamma 1 =
        mass2⁻¹ • ∫ q in interval2, (deriv fAtL q) • Gamma q l ∂volume ∧
      barGamma 2 =
        mass3⁻¹ • ∫ q in interval3, (deriv fAtL q) • Gamma q l ∂volume

end MathlibPlus.Open.Analysis.ResearchFormalizationR0192
