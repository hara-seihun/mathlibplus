import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Markov–Christoffel divided-kernel bound. -/
def markovChristoffelDividedKernelBound : Prop :=
  ∀ (N : ℕ) (A B : ℝ) (ν : Measure ℝ)
    (x : Fin N → ℝ) (ψ : Fin N → Polynomial ℝ),
    B > A →
    ν Set.univ = 1 →
    Measure.support ν = Set.range x →
    Function.Injective x →
    (∀ i : Fin N, x i ∈ Set.Icc A B) →
    ((∀ k : Fin N, (ψ k).degree = (k : WithBot ℕ)) ∧
      (∀ k : Fin N, Integrable (fun z : ℝ => (ψ k).eval z) ν) ∧
      (∀ k l : Fin N,
        ∫ z : ℝ, (ψ k).eval z * (ψ l).eval z ∂ν =
          if k = l then 1 else 0)) →
    ∀ d : ℕ, d < N →
      ∀ i j : Fin N, i ≠ j →
        (Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ d)).sum
          (fun k => (((ψ k).eval (x j) - (ψ k).eval (x i)) / (x i - x j)) ^ 2) ≤
          (4 * (d : ℝ) ^ 4 / (B - A) ^ 2) *
            sSup ((fun z : ℝ =>
              (Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ d)).sum
                (fun k => (ψ k).eval z ^ 2)) '' Set.Icc A B)

end MathlibPlus.Open.Analysis
