import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4301Claim51486

noncomputable section

open scoped BigOperators

/-- The address count in the recursive map-bank experiment. -/
def addressCount (a : ℕ) : ℕ := 2 ^ a

abbrev Address (a : ℕ) := Fin (addressCount a)
abbrev MapBitBank (a L : ℕ) :=
  Fin L → Address a → Fin a → Bool
abbrev TerminalSignBank (a : ℕ) := Address a → Bool
abbrev CompleteOracle (a L : ℕ) :=
  MapBitBank a L × TerminalSignBank a

/-- Decode the `a` fair bits encoding one map entry. -/
def decodeMapEntry {a : ℕ} (bits : Fin a → Bool) : Address a :=
  Fin.ofBits bits

/-- Apply the maps in their displayed order, with the zero-map convention. -/
def recursiveAddress (a : ℕ) : ∀ L : ℕ,
    (Fin L → Address a → Address a) → Address a → Address a
  | 0, _, x => x
  | n + 1, F, x =>
      recursiveAddress a n (fun i => F i.succ) (F 0 x)

/-- The address after the first `j` maps in a bank of length `L`. -/
def prefixAddress {a L : ℕ}
    (maps : Fin L → Address a → Address a)
    (j : ℕ) (h : j ≤ L) (x : Address a) : Address a :=
  recursiveAddress a j (fun i => maps (Fin.castLE h i)) x

/-- The concrete map bank decoded from the independent oracle bits. -/
def decodedMaps {a L : ℕ}
    (O : CompleteOracle a L) : Fin L → Address a → Address a :=
  fun i x => decodeMapEntry (O.1 i x)

/-- The terminal address reached from a starting address. -/
def terminalAddress {a L : ℕ}
    (O : CompleteOracle a L) (x : Address a) : Address a :=
  recursiveAddress a L (decodedMaps O) x

/-- The terminal sign, with the two signs represented by `-1` and `1`. -/
def terminalValue {a L : ℕ}
    (O : CompleteOracle a L) (x : Address a) : ℝ :=
  if O.2 (terminalAddress O x) then 1 else -1

/-- Uniform expectation on a finite type. -/
def finiteExpectation {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x : α, f x

/-- The conditional mean `g = E[Y | O]`, written as the exact finite
average over the independent uniform starting address. -/
def conditionalMean (a L : ℕ) (O : CompleteOracle a L) : ℝ :=
  finiteExpectation (fun x : Address a => terminalValue O x)

/-- Expectation and second moment of the oracle-measurable conditional mean. -/
def meanOfConditionalMean (a L : ℕ) : ℝ :=
  finiteExpectation (fun O : CompleteOracle a L => conditionalMean a L O)

def secondMomentOfConditionalMean (a L : ℕ) : ℝ :=
  finiteExpectation (fun O : CompleteOracle a L =>
    (conditionalMean a L O) ^ 2)

def varianceOfConditionalMean (a L : ℕ) : ℝ :=
  finiteExpectation (fun O : CompleteOracle a L =>
    (conditionalMean a L O - meanOfConditionalMean a L) ^ 2)

/-- The two-copy product expectation, using the same complete oracle bank. -/
def twoCopyProductExpectation (a L : ℕ) : ℝ :=
  finiteExpectation (fun O : CompleteOracle a L =>
    finiteExpectation (fun xx : Address a × Address a =>
      terminalValue O xx.1 * terminalValue O xx.2))

/-- The event containing the initial comparison and one noncollision event
for each of the `L` independent maps. -/
def twoCopyNoCollision {a L : ℕ}
    (O : CompleteOracle a L) (x x' : Address a) : Prop :=
  x ≠ x' ∧
    ∀ j : Fin L,
      prefixAddress (decodedMaps O) (j.val + 1)
          (Nat.succ_le_of_lt j.isLt) x ≠
        prefixAddress (decodedMaps O) (j.val + 1)
          (Nat.succ_le_of_lt j.isLt) x'

/-- Once two recursive addresses coalesce, the deterministic remaining maps
keep them equal. -/
def coalescencePersists {a L : ℕ} : Prop :=
  ∀ (O : CompleteOracle a L) (x x' : Address a)
    (j : ℕ) (h : j ≤ L),
    prefixAddress (decodedMaps O) j h x =
        prefixAddress (decodedMaps O) j h x' →
      terminalAddress O x = terminalAddress O x'

/-- The no-collision event is exactly terminal-address distinctness. -/
def terminalDistinctnessMatchesNoCollision {a L : ℕ} : Prop :=
  ∀ (O : CompleteOracle a L) (x x' : Address a),
    terminalAddress O x ≠ terminalAddress O x' ↔
      twoCopyNoCollision O x x'

/-- Probability of distinct terminal addresses in the two-copy experiment. -/
def terminalDistinctProbability (a L : ℕ) : ℝ :=
  finiteExpectation (fun O : CompleteOracle a L =>
    finiteExpectation (fun xx : Address a × Address a =>
      if terminalAddress O xx.1 ≠ terminalAddress O xx.2 then 1 else 0))

/-- The complete map-entry and terminal-sign bank is an independent fair-bit
oracle.  A map entry is decoded from the `a` bits in the corresponding block. -/
def independentFairOracleBits (a L : ℕ) : Prop :=
  ∀ (s : Finset (Sum (Fin L × Address a × Fin a) (Address a)))
    (b : Sum (Fin L × Address a × Fin a) (Address a) → Bool),
    finiteExpectation (fun O : CompleteOracle a L =>
      if ∀ i ∈ s,
          (match i with
          | Sum.inl j => O.1 j.1 j.2.1 j.2.2
          | Sum.inr x => O.2 x) = b i
      then 1 else 0) =
      (1 / 2 : ℝ) ^ s.card

/-- Distinct terminal-sign coordinates have the required fair independent law. -/
def independentDistinctTerminalSigns (a L : ℕ) : Prop :=
  (∀ x : Address a, ∀ b : Bool,
    finiteExpectation (fun O : CompleteOracle a L =>
      if O.2 x = b then 1 else 0) = (1 / 2 : ℝ)) ∧
  (∀ x x' : Address a, x ≠ x' → ∀ b b' : Bool,
    finiteExpectation (fun O : CompleteOracle a L =>
      if O.2 x = b ∧ O.2 x' = b' then 1 else 0) =
        (1 / 4 : ℝ))

/-- Claim 51486: the exact two-copy collision law and the conditional-mean
moment identities for the recursive map-bank channel. -/
def collisionFormula_claim51486 : Prop :=
  ∀ (a L : ℕ), 1 ≤ a →
    independentFairOracleBits a L ∧
      independentDistinctTerminalSigns a L ∧
      coalescencePersists (a := a) (L := L) ∧
      terminalDistinctnessMatchesNoCollision (a := a) (L := L) ∧
      terminalDistinctProbability a L =
        (1 - (1 : ℝ) / (addressCount a : ℝ)) ^ (L + 1) ∧
      meanOfConditionalMean a L = 0 ∧
      secondMomentOfConditionalMean a L =
        twoCopyProductExpectation a L ∧
      varianceOfConditionalMean a L =
        secondMomentOfConditionalMean a L ∧
      varianceOfConditionalMean a L =
        1 - (1 - (1 : ℝ) / (addressCount a : ℝ)) ^ (L + 1)

end

end MathlibPlus.Open.ResearchFormalization.R4301Claim51486
