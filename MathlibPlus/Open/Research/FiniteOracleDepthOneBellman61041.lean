import Mathlib

namespace MathlibPlus.Open.Research.FiniteOracleDepthOne

open scoped BigOperators
open MeasureTheory

abbrev RademacherSign := Bool
abbrev RademacherCube (I : Type*) := I → RademacherSign
abbrev OracleHistory (I : Type*) := I → Option RademacherSign

private def signReal (s : RademacherSign) : ℝ :=
  if s then 1 else -1

inductive DepthOneTree (I : Type*) where
  | constant (value : ℝ)
  | query (coordinate : I) (negativeValue positiveValue : ℝ)

private def depthOneTreeValue {I : Type*}
    (tree : DepthOneTree I) (x : RademacherCube I) : ℝ :=
  match tree with
  | DepthOneTree.constant value => value
  | DepthOneTree.query coordinate negativeValue positiveValue =>
      if x coordinate then positiveValue else negativeValue

private def depthOneTreeBounded {I : Type*} (tree : DepthOneTree I) : Prop :=
  match tree with
  | DepthOneTree.constant value => -1 ≤ value ∧ value ≤ 1
  | DepthOneTree.query _ negativeValue positiveValue =>
      -1 ≤ negativeValue ∧ negativeValue ≤ 1 ∧
        -1 ≤ positiveValue ∧ positiveValue ≤ 1

private def depthOneTreeMeasurableSpace (I : Type*) :
    MeasurableSpace (DepthOneTree I) :=
  ⊤

private def randomizedDepthOneRepresentation
    {I : Type*} [Fintype I]
    (F : RademacherCube I → ℝ)
    (ν : @Measure (DepthOneTree I) (depthOneTreeMeasurableSpace I)) : Prop :=
  (∀ᵐ tree ∂ν, depthOneTreeBounded tree) ∧
    ∀ x : RademacherCube I,
      F x = ∫ tree, depthOneTreeValue tree x ∂ν

private def finiteUniformRademacher
    {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) (O : I → Ω → RademacherSign) : Prop :=
  (∀ i : I, Measurable (O i)) ∧
    ∀ (s : Finset I) (ε : I → RademacherSign),
      μ {ω | ∀ i ∈ s, O i ω = ε i} =
        ((1 : ENNReal) / 2) ^ s.card

private noncomputable def compatibleOutcomes
    {I : Type*} [Fintype I]
    (h : OracleHistory I) : Finset (RademacherCube I) :=
  letI : Fintype (RademacherCube I) := Fintype.ofFinite (RademacherCube I)
  let p : RademacherCube I → Prop := fun x =>
    ∀ i : I, ∀ s : RademacherSign,
      h i = some s → x i = s
  letI : DecidablePred p := Classical.decPred p
  Finset.filter p Finset.univ

private noncomputable def finiteAverage {α : Type*} [Fintype α]
    (f : α → ℝ) (s : Finset α) : ℝ :=
  (s.card : ℝ)⁻¹ * s.sum f

private noncomputable def conditionalVariance
    {I : Type*} [Fintype I]
    (F : RademacherCube I → ℝ) (h : OracleHistory I) : ℝ :=
  letI : Fintype (RademacherCube I) := Fintype.ofFinite (RademacherCube I)
  let outcomes := compatibleOutcomes h
  let mean := finiteAverage F outcomes
  finiteAverage (fun x => (F x - mean) ^ 2) outcomes

private noncomputable def childHistory {I : Type*}
    (h : OracleHistory I) (i : I) (s : RademacherSign) : OracleHistory I :=
  letI : DecidableEq I := Classical.decEq I
  Function.update h i (some s)

private def rootHistory {I : Type*} : OracleHistory I :=
  fun _ => none

private noncomputable def activeCoordinates
    {I : Type*} [Fintype I]
    (a : I → ℝ) (h : OracleHistory I) : Finset I :=
  let p : I → Prop := fun i => h i = none ∧ a i ≠ 0
  letI : DecidablePred p := Classical.decPred p
  Finset.filter p Finset.univ

private noncomputable def sortedActiveCoefficients
    {I : Type*} [Fintype I]
    (a : I → ℝ) (h : OracleHistory I) : List ℝ :=
  Multiset.sort
    ((activeCoordinates a h).1.map (fun i => |a i|))
    (fun x y : ℝ => y ≤ x)

private noncomputable def rankedPotential
    {I : Type*} [Fintype I]
    (a : I → ℝ) (h : OracleHistory I) : ℝ :=
  ∑ k : Fin (sortedActiveCoefficients a h).length,
    ((k.1 + 1 : ℕ) : ℝ) *
      ((sortedActiveCoefficients a h).get k) ^ 2

private noncomputable def bellmanDepth
    {I : Type*} [Fintype I]
    (n : ℕ) (F : RademacherCube I → ℝ) : OracleHistory I → ℝ
  | h =>
      match n with
      | 0 => 0
      | n + 1 =>
          conditionalVariance F h +
            sInf {q : ℝ |
              ∃ i : I, h i = none ∧
                q =
                  (bellmanDepth n F (childHistory h i false) +
                    bellmanDepth n F (childHistory h i true)) / 2}

private noncomputable def bellmanValue
    {I : Type*} [Fintype I]
    (F : RademacherCube I → ℝ) (h : OracleHistory I) : ℝ :=
  bellmanDepth (Fintype.card I) F h

/-- The depth-one randomized-tree representation has the exact affine
coefficient certificate and the ranked Bellman value asserted in the packet. -/
def claim61041_depthOneRandomizedTreeBellman : Prop :=
  ∀ (I Ω : Type*) [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) (O : I → Ω → RademacherSign)
    (F : RademacherCube I → ℝ)
    (ν : @Measure (DepthOneTree I) (depthOneTreeMeasurableSpace I)),
    IsProbabilityMeasure μ →
      finiteUniformRademacher μ O →
        IsProbabilityMeasure ν →
          randomizedDepthOneRepresentation F ν →
            ∃ c : ℝ, ∃ a : I → ℝ,
              (∀ x : RademacherCube I,
                F x = c + ∑ i : I, a i * signReal (x i)) ∧
              (∀ ω : Ω,
                F (fun i => O i ω) =
                  c + ∑ i : I, a i * signReal (O i ω)) ∧
              (∑ i : I, |a i| ≤ 1) ∧
              (∀ h : OracleHistory I,
                bellmanValue F h = rankedPotential a h) ∧
              (∀ h : OracleHistory I,
                (activeCoordinates a h).Nonempty →
                  ∃ i : I,
                    i ∈ activeCoordinates a h ∧
                      (∀ j ∈ activeCoordinates a h, |a j| ≤ |a i|) ∧
                      bellmanValue F h =
                        conditionalVariance F h +
                          (bellmanValue F (childHistory h i false) +
                            bellmanValue F (childHistory h i true)) / 2) ∧
              rankedPotential a rootHistory ≤ 1

end MathlibPlus.Open.Research.FiniteOracleDepthOne
