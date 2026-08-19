import MathlibPlus.Open.ResearchFormalization.R61102Claim61102

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaFixedLevelMultiplexerClaim61120

noncomputable section

open Classical
open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R61102Claim61102

abbrev Coordinate := Fin 3
abbrev Policy := History → Option Coordinate

/-- The fixed target `1_{X=1}Y + 1_{X=-1}Z` on the three-bit Rademacher cube. -/
def multiplexerTarget (ω : Oracle) : ℝ :=
  (if ω 0 then (1 : ℝ) else 0) * signValue (ω 1) +
    (if ω 0 then (0 : ℝ) else 1) * signValue (ω 2)

/-- The one depth-two tree with `X` at level zero and the branch coordinate at
level one. -/
def fixedLevelMultiplexerTree : DecisionTree 3 :=
  .query 0
    (.query 2 (.leaf (-1 : ℝ)) (.leaf (1 : ℝ)))
    (.query 1 (.leaf (-1 : ℝ)) (.leaf (1 : ℝ)))

def treeDepth : DecisionTree 3 → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue => 1 + max (treeDepth ifFalse) (treeDepth ifTrue)

/-- The concrete tree realizes the target and has the fixed two-level shape. -/
def fixedLevelTree : Prop :=
  noRepeat fixedLevelMultiplexerTree ∧
    treeDepth fixedLevelMultiplexerTree = 2 ∧
      ∀ ω : Oracle,
        DecisionTree.evaluate fixedLevelMultiplexerTree ω = multiplexerTarget ω

/-- A transcript cell determines the target exactly when the target is constant
on all compatible oracle outcomes. -/
def targetMeasurableAt (h : History) : Prop :=
  ∀ x y : Oracle,
    consistent h x → consistent h y →
      multiplexerTarget x = multiplexerTarget y

/-- The first coordinate not yet revealed in a fixed oracle-independent order. -/
def nextUnseen (order : Equiv.Perm Coordinate) (h : History) : Option Coordinate :=
  if h (order 0) = none then some (order 0)
  else if h (order 1) = none then some (order 1)
  else if h (order 2) = none then some (order 2)
  else none

/-- Convert the function carrier used for finite randomized laws to the
reviewed coordinate-policy carrier. -/
def asCoordinatePolicy (π : Policy) : CoordinatePolicy :=
  ⟨π⟩

def policyLegal (π : Policy) : Prop :=
  legalPolicy (asCoordinatePolicy π)

def policyDetermines (π : Policy) : Prop :=
  ∀ ω : Oracle, ∃ n : ℕ, ∀ η : Oracle,
    consistent (transcript (asCoordinatePolicy π) ω n) η →
      multiplexerTarget η = multiplexerTarget ω

def policyArea (π : Policy) : ℝ :=
  rootInclusiveArea (asCoordinatePolicy π) multiplexerTarget

/-- A fixed order is followed until the target is measurable; extra behavior
after that time is irrelevant to the area. -/
def fixedOrderPolicy (order : Equiv.Perm Coordinate) : Policy :=
  fun h =>
    if targetMeasurableAt h then none
    else nextUnseen order h

/-- Nonadaptivity means that one order independent of the oracle controls
all reveals, with stopping allowed once the target is measurable. -/
def nonadaptivePolicy (π : Policy) : Prop :=
  ∃ order : Equiv.Perm Coordinate,
    ∀ h : History,
      (¬ targetMeasurableAt h →
        π h = nextUnseen order h) ∧
      (targetMeasurableAt h →
        π h = none ∨ π h = nextUnseen order h)

/-- An oracle-independent randomized nonadaptive law, with legal determining
policies on its positive-mass support. -/
def randomizedNonadaptiveLaw (p : Policy → ℝ) : Prop :=
  (∀ π, 0 ≤ p π) ∧
    (∑ π : Policy, p π = 1) ∧
      (∀ π, p π ≠ 0 →
        nonadaptivePolicy π ∧ policyLegal π ∧ policyDetermines π)

def randomizedNonadaptiveArea (p : Policy → ℝ) : ℝ :=
  ∑ π : Policy, p π * policyArea π

/-- The legal branch-selected policy: reveal `X`, then the active one of `Y`
and `Z`. -/
def adaptivePolicy : Policy :=
  fun h =>
    match h 0 with
    | none => some 0
    | some x =>
        if x then
          if h 1 = none then some 1 else none
        else if h 2 = none then some 2 else none

def deterministicOrderArea (order : Equiv.Perm Coordinate) : ℝ :=
  policyArea (fixedOrderPolicy order)

/-- Claim 61120: the exact fixed-level multiplexer separates all legal
oracle-independent randomized orders at `9/4` from the adaptive area `2`. -/
def claim61120 : Prop :=
  fixedLevelTree ∧
    (∀ p : Policy → ℝ,
      randomizedNonadaptiveLaw p →
        (9 : ℝ) / 4 ≤ randomizedNonadaptiveArea p) ∧
    (∀ order : Equiv.Perm Coordinate,
      order 0 = 0 → deterministicOrderArea order = (5 : ℝ) / 2) ∧
    (∀ order : Equiv.Perm Coordinate,
      order 0 ≠ 0 → deterministicOrderArea order = (9 : ℝ) / 4) ∧
    policyLegal adaptivePolicy ∧
      policyDetermines adaptivePolicy ∧
        policyArea adaptivePolicy = 2 ∧
          ¬ (∃ p : Policy → ℝ,
            randomizedNonadaptiveLaw p ∧
              randomizedNonadaptiveArea p ≤ 2)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaFixedLevelMultiplexerClaim61120
