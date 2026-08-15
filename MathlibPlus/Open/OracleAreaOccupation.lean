import Mathlib

namespace MathlibPlus.Open.OracleAreaOccupation

open scoped BigOperators

abbrev Coordinate (n : ℕ) := Fin n
abbrev Sign := {x : ℝ // x ∈ ({(-1 : ℝ), 1} : Finset ℝ)}

noncomputable instance signFintype : Fintype Sign := by
  classical
  infer_instance

abbrev Configuration (n : ℕ) := Coordinate n → Sign

def signValue (ε : Sign) : ℝ := ε.1

def negativeSign : Sign := ⟨-1, by simp⟩

def positiveSign : Sign := ⟨1, by simp⟩

def PartialAssignment (n : ℕ) (S : Finset (Coordinate n)) :=
  {i : Coordinate n // i ∈ S} → Sign

noncomputable instance partialAssignmentFintype (n : ℕ)
    (S : Finset (Coordinate n)) : Fintype (PartialAssignment n S) := by
  classical
  unfold PartialAssignment
  infer_instance

def TranscriptState (n : ℕ) :=
  Σ S : Finset (Coordinate n), PartialAssignment n S

noncomputable instance transcriptStateFintype (n : ℕ) : Fintype (TranscriptState n) := by
  classical
  unfold TranscriptState
  infer_instance

def IsProper (s : TranscriptState n) : Prop := s.1.card < n

def IsFull (s : TranscriptState n) : Prop := s.1.card = n

abbrev ProperState (n : ℕ) := {s : TranscriptState n // IsProper s}

noncomputable instance properStateFintype (n : ℕ) : Fintype (ProperState n) := by
  classical
  infer_instance

def Unrevealed (s : TranscriptState n) :=
  {i : Coordinate n // i ∉ s.1}

noncomputable instance unrevealedFintype (s : TranscriptState n) :
    Fintype (Unrevealed s) := by
  classical
  unfold Unrevealed
  infer_instance

def rootState : TranscriptState n :=
  ⟨∅, fun i => by
    exact nomatch i⟩

def child (s : TranscriptState n) (i : Coordinate n) (hi : i ∉ s.1)
    (ε : Sign) : TranscriptState n :=
  ⟨insert i s.1,
    fun k =>
      if hki : (k : Coordinate n) = i then ε
      else s.2 ⟨k, (Finset.mem_insert.mp k.property).resolve_left hki⟩⟩

def predecessor (s : TranscriptState n) (j : Coordinate n) (hj : j ∈ s.1) :
    TranscriptState n :=
  ⟨s.1.erase j,
    fun k => s.2 ⟨k, Finset.mem_of_mem_erase k.property⟩⟩

def predecessorProper (s : ProperState n)
    (j : {j : Coordinate n // j ∈ s.1.1}) : ProperState n :=
  ⟨predecessor s.1 j.1 j.2, by
    have hle : (s.1.1.erase j.1).card ≤ s.1.1.card := Finset.card_erase_le
    exact lt_of_le_of_lt hle s.2⟩

def predecessorAction (s : ProperState n)
    (j : {j : Coordinate n // j ∈ s.1.1}) :
    Unrevealed (predecessor s.1 j.1 j.2) :=
  ⟨j.1, by simp [predecessor]⟩

structure Simplex (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonnegative : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

abbrev RandomizedPolicy (n : ℕ) :=
  ∀ s : ProperState n, Simplex (Unrevealed s.1)

abbrev DeterministicPolicy (n : ℕ) :=
  ∀ s : ProperState n, Unrevealed s.1

noncomputable def diracSimplex {α : Type*} [Fintype α] (a₀ : α) : Simplex α := by
  classical
  refine { weight := fun a => if a = a₀ then 1 else 0, nonnegative := ?_, total := ?_ }
  · intro a
    by_cases h : a = a₀ <;> simp [h]
  · simp

noncomputable def deterministicKernel (d : DeterministicPolicy n) : RandomizedPolicy n :=
  fun s => diracSimplex (d s)

def Consistent (s : TranscriptState n) (o : Configuration n) : Prop :=
  ∀ i (hi : i ∈ s.1), o i = s.2 ⟨i, hi⟩

noncomputable def uniformConditionalAverage (f : Configuration n → ℝ)
    (s : TranscriptState n) : ℝ := by
  classical
  exact ((2 : ℝ) ^ (n - s.1.card))⁻¹ *
    ∑ o : Configuration n, if Consistent s o then f o else 0

noncomputable def conditionalVariance (g : Configuration n → ℝ)
    (s : TranscriptState n) : ℝ :=
  let μ := uniformConditionalAverage g s
  uniformConditionalAverage (fun o => (g o - μ) ^ 2) s

noncomputable def policyValueProper (g : Configuration n → ℝ)
    (π : RandomizedPolicy n) (s : ProperState n) : ℝ := by
  classical
  exact conditionalVariance g s.1 +
    ∑ a : Unrevealed s.1,
      (π s).weight a *
        (((if h : IsProper (child s.1 a.1 a.2 negativeSign) then
            policyValueProper g π ⟨child s.1 a.1 a.2 negativeSign, h⟩ else 0) +
          (if h : IsProper (child s.1 a.1 a.2 positiveSign) then
            policyValueProper g π ⟨child s.1 a.1 a.2 positiveSign, h⟩ else 0)) / 2)
  termination_by n - s.1.1.card
  decreasing_by
    all_goals
      have hs : s.1.1.card < n := s.2
      have hcard : (child s.1 a.1 a.2 negativeSign).1.card = s.1.1.card + 1 := by
        simp [child, a.2]
      have hcard' : (child s.1 a.1 a.2 positiveSign).1.card = s.1.1.card + 1 := by
        simp [child, a.2]
      omega

noncomputable def policyValue (g : Configuration n → ℝ)
    (π : RandomizedPolicy n) (s : TranscriptState n) : ℝ := by
  classical
  exact if h : IsProper s then policyValueProper g π ⟨s, h⟩ else 0

noncomputable def policyCost (g : Configuration n → ℝ)
    (π : RandomizedPolicy n) : ℝ := policyValue g π rootState

noncomputable def PolicyInf (g : Configuration n → ℝ) : ℝ :=
  sInf (Set.range (policyCost g))

abbrev ActionIndex (n : ℕ) :=
  Σ s : ProperState n, Unrevealed s.1

noncomputable instance actionIndexFintype (n : ℕ) : Fintype (ActionIndex n) := by
  classical
  unfold ActionIndex
  infer_instance

noncomputable def yAt (y : ActionIndex n → ℝ)
    (s : ProperState n) (a : Unrevealed s.1) : ℝ :=
  y ⟨s, a⟩

noncomputable def FlowEquation (y : ActionIndex n → ℝ) (s : ProperState n) : ℝ := by
  classical
  exact
    (∑ a : Unrevealed s.1, yAt y s a) -
      (1 / 2 : ℝ) *
        ∑ j : {j : Coordinate n // j ∈ s.1.1},
          yAt y (predecessorProper s j) (predecessorAction s j)

def NonnegativeOccupation (y : ActionIndex n → ℝ) : Prop :=
  ∀ a, 0 ≤ y a

def FlowFeasible (y : ActionIndex n → ℝ) : Prop := by
  classical
  exact ∀ s : ProperState n,
    FlowEquation y s = if s.1 = rootState then 1 else 0

def LPFeasible (y : ActionIndex n → ℝ) : Prop :=
  NonnegativeOccupation y ∧ FlowFeasible y

noncomputable def LPObjective (g : Configuration n → ℝ)
    (y : ActionIndex n → ℝ) : ℝ :=
  ∑ s : ProperState n,
    ∑ a : Unrevealed s.1, conditionalVariance g s.1 * yAt y s a

def DualPotential (n : ℕ) := TranscriptState n → ℝ

def DualBoundary (z : DualPotential n) : Prop :=
  ∀ s, IsFull s → z s = 0

def DualFeasible (g : Configuration n → ℝ) (z : DualPotential n) : Prop :=
  DualBoundary z ∧
    ∀ (s : ProperState n) (a : Unrevealed s.1),
      z s.1 -
          (z (child s.1 a.1 a.2 negativeSign) +
            z (child s.1 a.1 a.2 positiveSign)) / 2 ≤
        conditionalVariance g s.1

def DiagonalPSD (y : ActionIndex n → ℝ) : Prop := by
  classical
  exact ∀ u : ActionIndex n → ℝ,
    0 ≤ ∑ a : ActionIndex n, y a * (u a) ^ 2

def SDPFeasible (y : ActionIndex n → ℝ) : Prop :=
  DiagonalPSD y ∧ FlowFeasible y

def WalshCharacter (A : Finset (Coordinate n)) (o : Configuration n) : ℝ :=
  ∏ i : {i : Coordinate n // i ∈ A}, signValue (o i.1)

noncomputable def WalshCoefficient (g : Configuration n → ℝ)
    (A : Finset (Coordinate n)) : ℝ := by
  exact ((2 : ℝ) ^ n)⁻¹ *
    ∑ o : Configuration n, g o * WalshCharacter A o

def NormalizedWalshExpansion (g : Configuration n → ℝ) : Prop := by
  classical
  exact ∀ o, g o = ∑ A : Finset (Coordinate n),
    WalshCoefficient g A * WalshCharacter A o

def PartialCharacter (s : TranscriptState n)
    (C : Finset (Coordinate n)) : ℝ := by
  classical
  exact if hC : C ⊆ s.1 then
    ∏ i : {i : Coordinate n // i ∈ C},
      signValue (s.2 ⟨i.1, hC i.2⟩)
  else 0

noncomputable def PartialWalshCoefficient (g : Configuration n → ℝ)
    (s : TranscriptState n) (B : Finset (Coordinate n)) : ℝ := by
  classical
  exact ∑ C ∈ s.1.powerset,
    WalshCoefficient g (B ∪ C) * PartialCharacter s C

noncomputable def WalshSOSValue (g : Configuration n → ℝ)
    (s : TranscriptState n) : ℝ := by
  classical
  exact ∑ B ∈ (((Finset.univ \ s.1).powerset).erase ∅),
    (PartialWalshCoefficient g s B) ^ 2

def WalshSOSIdentity (g : Configuration n → ℝ) : Prop :=
  ∀ (s : ProperState n),
    conditionalVariance g s.1 = WalshSOSValue g s.1

def WalshCoefficientPSD (g : Configuration n → ℝ) : Prop :=
  ∀ s : ProperState n, 0 ≤ WalshSOSValue g s.1

def ExactOracleAreaOccupationLPSOS (n : ℕ)
    (g : Configuration n → ℝ) : Prop :=
  ∃ y : ActionIndex n → ℝ,
    LPFeasible y ∧
    (∀ y' : ActionIndex n → ℝ, LPFeasible y' → LPObjective g y ≤ LPObjective g y') ∧
    PolicyInf g = LPObjective g y ∧
    (∃ d : DeterministicPolicy n,
      policyCost g (deterministicKernel d) = LPObjective g y) ∧
    (∃ z : DualPotential n,
      DualFeasible g z ∧
      (∀ z', DualFeasible g z' → z' rootState ≤ z rootState) ∧
      z rootState = LPObjective g y) ∧
    (∀ y' : ActionIndex n → ℝ, LPFeasible y' ↔ SDPFeasible y') ∧
    NormalizedWalshExpansion g ∧
    WalshSOSIdentity g ∧
    WalshCoefficientPSD g

end MathlibPlus.Open.OracleAreaOccupation
