import MathlibPlus.Open.ResearchFormalization.R1397NormalizedShifts

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1397PureSection

open MathlibPlus.Open.ResearchFormalization.R1397NormalizedShifts

def shiftFunction (s : NormalizedShift) (u : ShiftBase) : NormalizedShift :=
  fun x => s (x + u)

def firstDifference (s : NormalizedShift) (u : ShiftBase) : NormalizedShift :=
  fun x => shiftFunction s u x - s x

/-- The actual mixed-second-difference relation module from the fixed genuine
C₃⁶ pair, including its central constant line. -/
def relationModule (s : NormalizedShift) : Submodule F3 NormalizedShift :=
  Submodule.span F3
    ({fun _ : ShiftBase => (1 : F3)} ∪
      {f | ∃ u v w : ShiftBase,
        f = shiftFunction (firstDifference (firstDifference s u) v) w})

/-- The literal pure quotient section criterion `(t-1)s ∈ K_s` for every
fixed-quotient translation t. -/
def literalPureQuotientSection (s : NormalizedShift) : Prop :=
  ∀ u : ShiftBase, firstDifference s u ∈ relationModule s

def affineLinearCoefficient (coeff : Fin 8 → F3) : Prop :=
  coeff (2 : Fin 8) = 0 ∧
    coeff (3 : Fin 8) = 0 ∧
    coeff (4 : Fin 8) = 0 ∧
    coeff (5 : Fin 8) = 0 ∧
    coeff (6 : Fin 8) = 0 ∧
    coeff (7 : Fin 8) = 0

/-- Claim 38594: in the exact normalized coefficient carrier for Record 6,
literal splitting is equivalent to vanishing of the six nonlinear/quadratic
coefficients, with exactly nine split and 6,552 nonsplit rows. -/
def affineShiftsAreExactlyPureSections_claim38594 : Prop :=
  (∀ coeff : Fin 8 → F3,
    normalized (shiftExpansion coeff) →
      (literalPureQuotientSection (shiftExpansion coeff) ↔
        affineLinearCoefficient coeff)) ∧
    Nat.card {coeff : Fin 8 → F3 //
      normalized (shiftExpansion coeff) ∧
        literalPureQuotientSection (shiftExpansion coeff)} = 9 ∧
    Nat.card {coeff : Fin 8 → F3 //
      normalized (shiftExpansion coeff) ∧
        ¬ literalPureQuotientSection (shiftExpansion coeff)} = 6552 ∧
    Nat.card {coeff : Fin 8 → F3 //
      normalized (shiftExpansion coeff) ∧
        affineLinearCoefficient coeff} = 9 ∧
    Nat.card {coeff : Fin 8 → F3 //
      normalized (shiftExpansion coeff) ∧
        ¬ affineLinearCoefficient coeff} = 6552

end MathlibPlus.Open.ResearchFormalization.R1397PureSection
