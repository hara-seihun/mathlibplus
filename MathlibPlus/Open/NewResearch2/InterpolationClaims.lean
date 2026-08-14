import Mathlib

namespace MathlibPlus.Open.NewResearch2.Interpolation

open scoped BigOperators
noncomputable section

abbrev NRNodeArray := ∀ n : ℕ, Fin (n + 1) → ℝ

def nrNodeArrayValid (a : NRNodeArray) : Prop :=
  (∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ n i j, i ≠ j → a n i ≠ a n j

def nrLagrangeBasis (a : NRNodeArray) (n : ℕ) (i : Fin (n + 1)) (x : ℝ) : ℝ := by
  classical
  exact ∏ j : Fin (n + 1),
    if j = i then 1 else (x - a n j) / (a n i - a n j)

def nrLebesgueFunction (a : NRNodeArray) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), |nrLagrangeBasis a n i x|

def nrLagrangeOperator (a : NRNodeArray) (f : ℝ → ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), f (a n i) * nrLagrangeBasis a n i x

def nrContinuousOnInterval (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Icc (-1 : ℝ) 1)

def nrLebesgueUnboundedAt (a : NRNodeArray) (x : ℝ) : Prop :=
  ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ C < nrLebesgueFunction a n x

def nrInterpolationDivergesAt (a : NRNodeArray) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    C < |nrLagrangeOperator a f n x|

def nrInterpolatesAt (a : NRNodeArray) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => nrLagrangeOperator a f n x)
    Filter.atTop (nhds (f x))

def nrWeakErdos671 (a : NRNodeArray) : Prop :=
  nrNodeArrayValid a ∧
    ∀ f : ℝ → ℝ, nrContinuousOnInterval f →
      ∃ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 ∧
        nrLebesgueUnboundedAt a x ∧ nrInterpolatesAt a f x

def nrStrongErdos671 (a : NRNodeArray) : Prop :=
  nrNodeArrayValid a ∧
    (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → nrLebesgueUnboundedAt a x) ∧
    (∀ f : ℝ → ℝ, nrContinuousOnInterval f →
      ∃ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 ∧ nrInterpolatesAt a f x)

def nrUnavoidableLebesgueUnboundedness : Prop :=
  ∀ a : NRNodeArray, nrNodeArrayValid a →
    ∃ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 ∧ nrLebesgueUnboundedAt a x

def nrAlmostEverywhereDivergence : Prop :=
  ∀ a : NRNodeArray, nrNodeArrayValid a →
    ∃ f : ℝ → ℝ, nrContinuousOnInterval f ∧
      ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1),
        nrInterpolationDivergesAt a f x

def claim16704 : Prop :=
  ∃ a : NRNodeArray, nrWeakErdos671 a

def claim16705 : Prop :=
  ∃ a : NRNodeArray, nrStrongErdos671 a

def claim16707 : Prop :=
  nrUnavoidableLebesgueUnboundedness

def claim16708 : Prop :=
  nrAlmostEverywhereDivergence

def claim16709 : Prop :=
  ∀ a : NRNodeArray, nrStrongErdos671 a → nrWeakErdos671 a

end

end MathlibPlus.Open.NewResearch2.Interpolation
