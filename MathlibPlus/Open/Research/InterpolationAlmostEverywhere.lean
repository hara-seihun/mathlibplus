import Mathlib

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace MathlibPlus.Open.Research

abbrev ResearchInterval := Set.Icc (-1 : ℝ) 1
abbrev ResearchNode := ResearchInterval
abbrev ResearchNodeArray := ∀ n : ℕ, Fin (n + 1) → ResearchNode
abbrev ResearchFunction := ContinuousMap ResearchInterval ℝ

def RowwiseDistinct (X : ResearchNodeArray) : Prop :=
  ∀ n, Function.Injective (X n)

def LagrangeBasis (X : ResearchNodeArray) (n : ℕ) (j : Fin (n + 1)) (x : ℝ) : ℝ :=
  ∏ k : Fin (n + 1),
    if k = j then 1
    else (x - (X n k : ℝ)) / ((X n j : ℝ) - (X n k : ℝ))

def LagrangeInterpolant (X : ResearchNodeArray) (f : ResearchFunction)
    (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), f (X n j) * LagrangeBasis X n j x

def LebesgueFunction (X : ResearchNodeArray) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), |LagrangeBasis X n j x|

def AlmostEverywhereOnResearchInterval (P : ℝ → Prop) : Prop :=
  ∀ᵐ x ∂Measure.restrict volume ResearchInterval, P x

def ArbitrarilyLateUnbounded (X : ResearchNodeArray) (x : ℝ) : Prop :=
  ∀ M : ℝ, ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ M < LebesgueFunction X n x

def claim46542 : Prop :=
  ∃ X : ResearchNodeArray,
    RowwiseDistinct X ∧
      (∀ x : ResearchInterval, ArbitrarilyLateUnbounded X (x : ℝ)) ∧
      (∀ f : ResearchFunction, ∃ x : ResearchInterval,
        Tendsto (fun n : ℕ => LagrangeInterpolant X f n (x : ℝ)) atTop (𝓝 (f x)) ∧
          ArbitrarilyLateUnbounded X (x : ℝ))

def claim46557 : Prop :=
  ∀ X : ResearchNodeArray, RowwiseDistinct X →
    ∃ f : ResearchFunction,
      AlmostEverywhereOnResearchInterval
        (fun x : ℝ => Tendsto (fun n : ℕ =>
          |LagrangeInterpolant X f n x|) atTop atTop)

def claim46562 : Prop :=
  ∀ X : ResearchNodeArray, RowwiseDistinct X →
    AlmostEverywhereOnResearchInterval
      (fun x : ℝ => Tendsto (fun n : ℕ => LebesgueFunction X n x) atTop atTop)

end MathlibPlus.Open.Research
