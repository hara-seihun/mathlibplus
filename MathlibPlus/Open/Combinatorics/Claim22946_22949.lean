import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

/-- The three explicitly named blocks, indexed only to state the symmetric
pair and singleton layers. -/
def blockAt {α : Type*} [DecidableEq α]
    (M₁ M₂ M₃ : Finset α) (i : Fin 3) : Finset α :=
  if i = 0 then M₁ else if i = 1 then M₂ else M₃

/-- The nine-point carrier is exactly the disjoint union of the three
three-point blocks.  The ambient coordinate type is not restricted to these
nine points. -/
def threeBlockCarrier {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) : Prop :=
  K = (M₁ ∪ M₂) ∪ M₃ ∧
    M₁.card = 3 ∧ M₂.card = 3 ∧ M₃.card = 3 ∧
      M₁ ∩ M₂ = ∅ ∧ M₁ ∩ M₃ = ∅ ∧ M₂ ∩ M₃ = ∅

/-- The local permitted-trace hypotheses on the exact carrier. -/
def localTraceConditions {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) (H : Finset (Finset α)) : Prop :=
  H.Nonempty ∧
    (∀ S ∈ H, S ⊆ K) ∧
      (∀ S ∈ H, S.Nonempty →
        ∃ i : Fin 3, blockAt M₁ M₂ M₃ i ⊆ S) ∧
        (∀ S ∈ H, ∀ i : Fin 3,
          S ∪ blockAt M₁ M₂ M₃ i ∈ H)

/-- The integer charge q(S) = 2|S| - 9. -/
def traceCharge {α : Type*} (S : Finset α) : ℤ :=
  2 * (S.card : ℤ) - 9

def totalTraceCharge {α : Type*}
    (H : Finset (Finset α)) : ℤ :=
  ∑ S ∈ H, traceCharge S

/-- The 0/1 membership indicator of a named trace. -/
def membershipIndicator {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (S : Finset α) : ℤ :=
  if S ∈ H then 1 else 0

def pairIndex3 : Finset (Fin 3 × Fin 3) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2)

def bareIndicatorSum {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (M₁ M₂ M₃ : Finset α) : ℤ :=
  ∑ i : Fin 3, membershipIndicator H (blockAt M₁ M₂ M₃ i)

def pairIndicatorSum {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (M₁ M₂ M₃ : Finset α) : ℤ :=
  ∑ p ∈ pairIndex3,
    membershipIndicator H
      (blockAt M₁ M₂ M₃ p.1 ∪ blockAt M₁ M₂ M₃ p.2)

/-- A bare block or a one-point extension by a point from another block,
including the two stated charge values. -/
def negativeTraceShape {α : Type*} [DecidableEq α]
    (M₁ M₂ M₃ S : Finset α) : Prop :=
  (∃ i : Fin 3,
    S = blockAt M₁ M₂ M₃ i ∧ traceCharge S = -3) ∨
    (∃ (i j : Fin 3) (x : α),
      i ≠ j ∧ x ∈ blockAt M₁ M₂ M₃ j ∧
        S = blockAt M₁ M₂ M₃ i ∪ {x} ∧ traceCharge S = -1)

/-- The possible negative singleton-layer traces for a fixed point x in block j. -/
def negativeSingletonIndices {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (M₁ M₂ M₃ : Finset α)
    (j : Fin 3) (x : α) : Finset (Fin 3) :=
  (Finset.univ : Finset (Fin 3)).filter (fun i =>
    i ≠ j ∧
      blockAt M₁ M₂ M₃ i ∪ {x} ∈ H ∧
        traceCharge (blockAt M₁ M₂ M₃ i ∪ {x}) = -1)

/-- The common seven-point recipient for a point x in block j. -/
def sevenPointRecipient {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) (j : Fin 3) (x : α) : Finset α :=
  (K \ blockAt M₁ M₂ M₃ j) ∪ {x}

/-- Claim 22946: completion stability, with no full union-closure premise,
gives the two sharp local charge bounds. -/
def completionOnlyLocalCharge_claim22946 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) (H : Finset (Finset α)),
    threeBlockCarrier K M₁ M₂ M₃ →
      localTraceConditions K M₁ M₂ M₃ H →
        ((∅ : Finset α) ∉ H → 9 ≤ totalTraceCharge H) ∧
          ((∅ : Finset α) ∈ H → 0 ≤ totalTraceCharge H)

/-- Claim 22947: under the local permitted-trace conditions, negative charge
has exactly the two stated shapes, and every other nonempty trace is at least
five-point and nonnegative. -/
def negativeTraceClassification_claim22947 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) (H : Finset (Finset α)),
    threeBlockCarrier K M₁ M₂ M₃ →
      localTraceConditions K M₁ M₂ M₃ H →
        ∀ S ∈ H, S.Nonempty →
          (traceCharge S < 0 →
            negativeTraceShape M₁ M₂ M₃ S) ∧
            (¬ negativeTraceShape M₁ M₂ M₃ S →
              5 ≤ S.card ∧ 0 ≤ traceCharge S)

/-- Claim 22948: pair completions give the two indicator inequalities for
already present bare blocks, and the resulting pair-charge coverage bound. -/
def pairTracesPayBareDeficits_claim22948 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) (H : Finset (Finset α)),
    threeBlockCarrier K M₁ M₂ M₃ →
      (∀ S ∈ H, ∀ i : Fin 3,
        S ∪ blockAt M₁ M₂ M₃ i ∈ H) →
        (∀ (i j k : Fin 3),
          i ≠ j → i ≠ k → j ≠ k →
            blockAt M₁ M₂ M₃ i ∈ H →
              blockAt M₁ M₂ M₃ i ∪ blockAt M₁ M₂ M₃ j ∈ H ∧
                traceCharge
                    (blockAt M₁ M₂ M₃ i ∪ blockAt M₁ M₂ M₃ j) = 3 ∧
                blockAt M₁ M₂ M₃ i ∪ blockAt M₁ M₂ M₃ k ∈ H ∧
                traceCharge
                    (blockAt M₁ M₂ M₃ i ∪ blockAt M₁ M₂ M₃ k) = 3) ∧
          (∀ (i j k : Fin 3),
            i ≠ j → i ≠ k → j ≠ k →
              2 * membershipIndicator H (blockAt M₁ M₂ M₃ i) ≤
                membershipIndicator H
                    (blockAt M₁ M₂ M₃ i ∪ blockAt M₁ M₂ M₃ j) +
                  membershipIndicator H
                    (blockAt M₁ M₂ M₃ i ∪ blockAt M₁ M₂ M₃ k)) ∧
          3 * bareIndicatorSum H M₁ M₂ M₃ ≤
            3 * pairIndicatorSum H M₁ M₂ M₃

/-- Claim 22949: the at-most-two singleton layer has a common seven-point
recipient of charge five, and recipient equality is injective when both
points are known to lie in their named blocks. -/
def sevenPointTracesPaySingletons_claim22949 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (K M₁ M₂ M₃ : Finset α) (H : Finset (Finset α)),
    threeBlockCarrier K M₁ M₂ M₃ →
      (∀ S ∈ H, ∀ i : Fin 3,
        S ∪ blockAt M₁ M₂ M₃ i ∈ H) →
        (∀ (j : Fin 3) (x : α), x ∈ blockAt M₁ M₂ M₃ j →
          (negativeSingletonIndices H M₁ M₂ M₃ j x).card ≤ 2 ∧
            (∀ i ∈ negativeSingletonIndices H M₁ M₂ M₃ j x,
              ∃ k : Fin 3,
                k ≠ i ∧ k ≠ j ∧
                  (blockAt M₁ M₂ M₃ i ∪ {x}) ∪
                      blockAt M₁ M₂ M₃ k ∈ H ∧
                  (blockAt M₁ M₂ M₃ i ∪ {x}) ∪
                      blockAt M₁ M₂ M₃ k =
                    sevenPointRecipient K M₁ M₂ M₃ j x ∧
                  sevenPointRecipient K M₁ M₂ M₃ j x ∈ H ∧
                  traceCharge
                    (sevenPointRecipient K M₁ M₂ M₃ j x) = 5)) ∧
        (∀ (j j' : Fin 3) (x x' : α),
          x ∈ blockAt M₁ M₂ M₃ j →
            x' ∈ blockAt M₁ M₂ M₃ j' →
              sevenPointRecipient K M₁ M₂ M₃ j x =
                  sevenPointRecipient K M₁ M₂ M₃ j' x' →
                j = j' ∧ x = x')

end MathlibPlus.Open.Combinatorics
