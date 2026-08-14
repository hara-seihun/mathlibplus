import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace MathlibPlus
namespace Open
namespace Probability

abbrev Sign := Fin 2

/-- The two signs, represented by `0,1 : Fin 2` and evaluated as `-1,1`. -/
def signValue (s : Sign) : ℝ := 2 * (s.1 : ℝ) - 1

inductive SignDecisionTree (I : Type*) where
  | leaf (value : Sign)
  | node (coordinate : I) (low high : SignDecisionTree I)

namespace SignDecisionTree

def depth : SignDecisionTree I → ℕ
  | .leaf _ => 0
  | .node _ low high => max low.depth high.depth + 1

def evaluate (tree : SignDecisionTree I) (oracle : I → Sign) : Sign :=
  match tree with
  | .leaf value => value
  | .node coordinate low high =>
      if oracle coordinate = 0 then low.evaluate oracle else high.evaluate oracle

noncomputable def queriedCoordinates (tree : SignDecisionTree I) : Finset I := by
  classical
  induction tree with
  | leaf value => exact ∅
  | node coordinate low high ihLow ihHigh =>
      exact insert coordinate (ihLow ∪ ihHigh)

end SignDecisionTree

structure FiniteProbabilityLaw (α : Type*) where
  support : Finset α
  weight : α → NNReal
  mem_support_iff_pos : ∀ a, a ∈ support ↔ 0 < weight a
  total_weight : support.sum (fun a => weight a) = 1

def lawExpectation {α : Type*} (Λ : FiniteProbabilityLaw α) (f : α → ℝ) : ℝ :=
  Λ.support.sum (fun a => (Λ.weight a : ℝ) * f a)

def essentialCoordinates {I : Type*} (T : (I → Sign) → Sign) : Set I :=
  {i | ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ T x ≠ T y}

def relevantCoordinates {I : Type*}
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign)) : Set I :=
  {i | ∃ T ∈ Λ.support, i ∈ essentialCoordinates T}

def admissibleTreeLaw {I : Type*}
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign)) : Prop :=
  ∀ T ∈ Λ.support,
    Monotone T ∧
      ∃ tree : SignDecisionTree I,
        tree.depth ≤ 2 ∧ tree.evaluate = T

def mixtureMean {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign))
    (O : I → Ω → Sign) : Ω → ℝ :=
  fun ω => lawExpectation Λ (fun T => signValue (T (fun i => O i ω)))

def uniformIndependentSigns {I Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (O : I → Ω → Sign) : Prop :=
  (∀ i, Measurable (O i)) ∧
    ProbabilityTheory.iIndepFun O P ∧
      ∀ i s, P {ω | O i ω = s} = (1 / 2 : ℝ≥0∞)

def prefixOracle {I Ω : Type*} [MeasurableSpace Ω]
    (O : I → Ω → Sign) (order : Fin N → I) (m : ℕ) :
    Ω → (Fin (min m N) → Sign) :=
  fun ω j =>
    O (order ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.min_le_right m N)⟩) ω

def revealFiltration {I Ω : Type*} [MeasurableSpace Ω]
    (O : I → Ω → Sign) (order : Fin N → I) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (prefixOracle O order m) MeasurableSpace.pi

def stopsWhenMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (filtration : ℕ → MeasurableSpace Ω) (μ : Ω → ℝ) (stop : ℕ) : Prop :=
  @Measurable Ω ℝ (filtration stop) inferInstance μ ∧
    ∀ m < stop, ¬ @Measurable Ω ℝ (filtration m) inferInstance μ

noncomputable def stoppedVarianceSum {Ω : Type*} [MeasurableSpace Ω]
    (filtration : ℕ → MeasurableSpace Ω) (μ : Ω → ℝ)
    (P : Measure Ω) (stop : ℕ) : ℝ :=
  (Finset.range (stop + 1)).sum (fun m =>
    ∫ ω, ProbabilityTheory.condVar (filtration m) μ P ω ∂P)

def admissibleOrdering {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign))
    (O : I → Ω → Sign) (N : ℕ) (order : Fin N → I) (stop : ℕ) : Prop :=
  Function.Injective order ∧
    Set.range order = relevantCoordinates Λ ∧
      stopsWhenMeasurable (revealFiltration O order) (mixtureMean Λ O) stop

noncomputable def pointMass {α : Type*} (a : α) : FiniteProbabilityLaw α := by
  classical
  refine
    { support := {a}
      weight := fun b => if b = a then 1 else 0
      mem_support_iff_pos := ?_
      total_weight := ?_ }
  · intro b
    by_cases h : b = a
    · simp [h]
    · simp [h]
  · simp

def twoCoordinateAnd (x : Fin 2 → Sign) : Sign :=
  if x 0 = 1 ∧ x 1 = 1 then 1 else 0

def twoCoordinateOr (x : Fin 2 → Sign) : Sign :=
  if x 0 = 1 ∨ x 1 = 1 then 1 else 0

def sharpForTwoCoordinateFunction
    (f : (Fin 2 → Sign) → Sign) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
      letI : IsProbabilityMeasure P := hP
      ∃ (O : Fin 2 → Ω → Sign) (N : ℕ) (order : Fin N → Fin 2) (stop : ℕ),
        uniformIndependentSigns P O ∧
          admissibleOrdering (pointMass f) O N order stop ∧
            stoppedVarianceSum (revealFiltration O order)
              (mixtureMean (pointMass f) O) P stop = (5 / 4 : ℝ)

/-- Claim 59857: the depth-two oracle variance bound and its sharpness. -/
def claim59857 : Prop :=
  (∀ (I : Type*) [Countable I]
      (Λ : FiniteProbabilityLaw ((I → Sign) → Sign)),
      admissibleTreeLaw Λ →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (O : I → Ω → Sign),
          uniformIndependentSigns P O →
            ∃ (N : ℕ) (order : Fin N → I) (stop : ℕ),
              admissibleOrdering Λ O N order stop ∧
                stoppedVarianceSum (revealFiltration O order)
                  (mixtureMean Λ O) P stop ≤ (5 / 4 : ℝ)) ∧
    sharpForTwoCoordinateFunction twoCoordinateAnd ∧
      sharpForTwoCoordinateFunction twoCoordinateOr

end Probability
end Open
end MathlibPlus
