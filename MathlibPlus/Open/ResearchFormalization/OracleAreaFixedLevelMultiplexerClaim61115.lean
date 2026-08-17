import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaFixedLevelMultiplexerClaim61115

noncomputable section

abbrev Outcome := Bool × Bool × Bool

/-- The two Rademacher values used by the target. -/
def rademacherValue : Bool → ℚ
  | false => -1
  | true => 1

/-- The fixed-level depth-two multiplexer target. -/
def multiplexerTarget : Outcome → ℚ
  | (x, y, z) => if x then rademacherValue y else rademacherValue z

/-- The coordinate labels are `0 = X`, `1 = Y`, and `2 = Z`. -/
def coordinateValue (ω : Outcome) (i : Fin 3) : Bool :=
  if i = 0 then ω.1 else if i = 1 then ω.2.1 else ω.2.2

/-- The coordinates revealed by a fixed coordinate order through time `t`. -/
def fixedOrderObservation (order : Equiv.Perm (Fin 3)) (t : ℕ)
    (ω : Outcome) : Fin 3 → Option Bool :=
  fun i =>
    if (order i).val < t then some (coordinateValue ω i) else none

/-- The actual fibre of an observation value. -/
def observationFiber {Ω β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq β] (obs : Ω → β) (ω : Ω) : Finset Ω :=
  (Finset.univ : Finset Ω).filter (fun η => obs η = obs ω)

/-- The conditional mean on the finite observation fibre. -/
def conditionalMean {Ω β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq β] (f : Ω → ℚ) (obs : Ω → β) (ω : Ω) : ℚ :=
  (∑ η ∈ observationFiber obs ω, f η) /
    (observationFiber obs ω).card

/-- The conditional variance on the finite observation fibre. -/
def conditionalVarianceAt {Ω β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq β] (f : Ω → ℚ) (obs : Ω → β) (ω : Ω) : ℚ :=
  (∑ η ∈ observationFiber obs ω,
    (f η - conditionalMean f obs ω) ^ 2) /
      (observationFiber obs ω).card

/-- Expected posterior variance for an exact finite observation. -/
def expectedConditionalVariance {Ω β : Type*} [Fintype Ω]
    [DecidableEq Ω] [DecidableEq β] (f : Ω → ℚ) (obs : Ω → β) : ℚ :=
  (1 / (Fintype.card Ω : ℚ)) *
    ∑ ω : Ω, conditionalVarianceAt f obs ω

/-- The root-inclusive area of a fixed nonadaptive coordinate order. -/
def nonadaptiveArea (order : Equiv.Perm (Fin 3)) : ℚ :=
  ∑ t ∈ Finset.range 3,
    expectedConditionalVariance multiplexerTarget
      (fixedOrderObservation order t)

/-- A randomized nonadaptive policy is an oracle-independent probability law
on the six fixed coordinate orders. -/
def orderLaw (w : Equiv.Perm (Fin 3) → ℚ) : Prop :=
  (∀ order, 0 ≤ w order) ∧
    (∑ order : Equiv.Perm (Fin 3), w order) = 1

/-- The expected area of a randomized nonadaptive policy. -/
def randomizedNonadaptiveArea
    (w : Equiv.Perm (Fin 3) → ℚ) : ℚ :=
  ∑ order : Equiv.Perm (Fin 3), w order * nonadaptiveArea order

/-- The second observation of the legal adaptive policy: after revealing `X`,
reveal the branch-selected one of `Y` and `Z`. -/
def adaptiveSecondObservation : Outcome → Bool × Bool
  | (x, y, z) => (x, if x then y else z)

/-- The root-inclusive area of the actual adaptive multiplexer policy. -/
def adaptiveArea : ℚ :=
  expectedConditionalVariance multiplexerTarget (fun _ : Outcome => ()) +
    expectedConditionalVariance multiplexerTarget (fun ω : Outcome => ω.1) +
      expectedConditionalVariance multiplexerTarget adaptiveSecondObservation

/-- Claim 61115: every oracle-independent randomized order has area at least
`9/4`, every fixed order that does not reveal `X` first attains that value,
and the legal adaptive branch-selected policy has area exactly `2`. -/
def claim61115 : Prop :=
  (∀ w : Equiv.Perm (Fin 3) → ℚ,
    orderLaw w →
      (9 : ℚ) / 4 ≤ randomizedNonadaptiveArea w) ∧
  (∀ order : Equiv.Perm (Fin 3), order 0 ≠ 0 →
    nonadaptiveArea order = (9 : ℚ) / 4) ∧
  adaptiveArea = 2 ∧
  ¬ (∃ w : Equiv.Perm (Fin 3) → ℚ,
    orderLaw w ∧ randomizedNonadaptiveArea w ≤ 2)

end
end MathlibPlus.Open.ResearchFormalization.OracleAreaFixedLevelMultiplexerClaim61115
