import Mathlib

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The finite sign cube for the `n` cancelled coordinates and the exceptional
coordinate `y`.  A Boolean sign is evaluated as a Rademacher sign. -/
def CubeState (n : ℕ) := Fin (n + 1) → Bool

def signValue (s : Bool) : ℝ := if s then 1 else -1

/-- The two literal components belonging to a cancelled coordinate. -/
def plusLiteral {n : ℕ} (j : Fin n) (ω : CubeState n) : ℝ :=
  signValue (ω j.castSucc)

def minusLiteral {n : ℕ} (j : Fin n) (ω : CubeState n) : ℝ :=
  -signValue (ω j.castSucc)

/-- The exceptional depth-one component `H=y`. -/
def headLiteral {n : ℕ} (ω : CubeState n) : ℝ :=
  signValue (ω (Fin.last n))

/-- The common weight of each of the two labels for one cancelled coordinate. -/
def pairWeight (n : ℕ) (ε : ℝ) : ℝ :=
  (1 - ε) / (2 * (n : ℝ))

/-- The signed target of the displayed literal-pair family. -/
def cancelledLiteralTarget (n : ℕ) (ε : ℝ) (ω : CubeState n) : ℝ :=
  Finset.sum Finset.univ (fun j : Fin n =>
      pairWeight n ε * plusLiteral j ω +
        pairWeight n ε * minusLiteral j ω) +
    ε * headLiteral ω

/-- The exact cancellation and weight assertions for the family used by the
comparison.  The cube is the finite model of independent signs. -/
def cancelledLiteralFamily (n : ℕ) (ε : ℝ) : Prop :=
  2 ≤ n ∧
    0 < ε ∧ ε < 1 ∧
    Finset.sum Finset.univ (fun _j : Fin n =>
      (pairWeight n ε + pairWeight n ε)) + ε = 1 ∧
    (∀ ω : CubeState n,
      cancelledLiteralTarget n ε ω = ε * headLiteral ω)

/-- The aggregate fresh-coordinate rate of a cancelled pair. -/
def cancelledRate (n : ℕ) (ε : ℝ) : ℝ :=
  (1 - ε) / (n : ℝ)

/-- The exceptional fresh coordinate. -/
def yCoordinate (n : ℕ) : Fin (n + 1) := Fin.last n

/-- Rates of the fresh coordinates after the opposite label of a queried pair
is cached.  Thus the `n` cancelled coordinates have rate `r`, and `y` has rate
`ε`. -/
def freshRate (n : ℕ) (ε : ℝ) (i : Fin (n + 1)) : ℝ :=
  if i.val < n then cancelledRate n ε else ε

/-- The Plackett--Luce probability of a fresh-coordinate order.  At rank `k`
the denominator contains exactly the coordinates whose positions are at least
`k`; this is the sequential exponential-key law. -/
def freshOrderProbability (n : ℕ) (ε : ℝ)
    (π : Equiv.Perm (Fin (n + 1))) : ℝ :=
  ∏ k : Fin (n + 1),
    freshRate n ε (π k) /
      ∑ j : Fin (n + 1),
        if (π.symm j).val ≥ k.val then freshRate n ε j else 0

/-- The one-based fresh position of `y` in a fresh order. -/
def freshYPosition (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) : ℝ :=
  (((π.symm (yCoordinate n)).val + 1 : ℕ) : ℝ)

/-- Expected fresh position of `y` under the persistent Plackett--Luce order. -/
def expectedFreshYPosition (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin (n + 1)),
    freshOrderProbability n ε π * freshYPosition n π

/-- The posterior variance at a root-inclusive fresh-query time.  It is
`ε²` before `y` is queried and zero thereafter, exactly as in the admitted
calculation. -/
def posteriorVarianceAtFreshTime (n : ℕ) (ε : ℝ)
    (π : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 2)) : ℝ :=
  if t.val < (π.symm (yCoordinate n)).val + 1 then ε ^ 2 else 0

/-- The actual root-inclusive posterior-variance area of the exact family,
obtained by averaging the variance profile over the persistent
Plackett--Luce fresh orders. -/
def persistentPlackettLuceArea (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin (n + 1)),
    freshOrderProbability n ε π *
      ∑ t : Fin (n + 2), posteriorVarianceAtFreshTime n ε π t

/-- The closed expression supplied by the exact fresh-order calculation. -/
def closedPlackettLuceArea (n : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 *
    (1 + (n : ℝ) * cancelledRate n ε /
      (cancelledRate n ε + ε))

/-- Number of independently path-marked cancelled coordinates in a marking
of the `n` coordinates. -/
def markedCount {n : ℕ} (A : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if A i then 1 else 0

/-- The conditional inherited-order reserve bracket for a given marking. -/
def pathMarkedBracket (n : ℕ) (ε : ℝ) (A : Fin n → Bool) : ℝ :=
  1 +
    ((n - markedCount A : ℕ) : ℝ) * cancelledRate n ε /
      (ε + ((markedCount A + 1 : ℕ) : ℝ) * cancelledRate n ε)

/-- The inherited-order path-marked reserve as a uniform expectation over
independent fair markings. -/
def inheritedOrderPathMarkedReserve (n : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 *
    ∑ A : Fin n → Bool,
      (1 / (2 : ℝ) ^ n) * pathMarkedBracket n ε A

/-- The same reserve written with the `M ~ Bin(n,1/2)` law from the admitted
calculation. -/
def binomialPathMarkedReserve (n : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 *
    Finset.sum (Finset.range (n + 1)) (fun m =>
      ((Nat.choose n m : ℝ) / (2 : ℝ) ^ n) *
        (1 +
          ((n - m : ℕ) : ℝ) * cancelledRate n ε /
            (ε + ((m + 1 : ℕ) : ℝ) * cancelledRate n ε)))

/-- The prescribed specialization `ε=1/n`. -/
def familyEpsilon (n : ℕ) : ℝ :=
  1 / (n : ℝ)

def familyArea (n : ℕ) : ℝ :=
  persistentPlackettLuceArea n (familyEpsilon n)

def familyReserve (n : ℕ) : ℝ :=
  inheritedOrderPathMarkedReserve n (familyEpsilon n)

def familyRatio (n : ℕ) : ℝ :=
  familyArea n / familyReserve n

/-- Claim 53248: on the cancelled literal-pair family, with `ε=1/n`, the
actual persistent-Plackett--Luce area divided by the inherited-order
path-marked reserve is asymptotic to `n/4`, and therefore no universal
comparison constant exists. -/
def unboundedGlobalComparisonRatio : Prop :=
  (∀ n : ℕ, 2 ≤ n → cancelledLiteralFamily n (familyEpsilon n)) ∧
    (∀ n : ℕ, 2 ≤ n →
      persistentPlackettLuceArea n (familyEpsilon n) =
          closedPlackettLuceArea n (familyEpsilon n) ∧
        inheritedOrderPathMarkedReserve n (familyEpsilon n) =
          binomialPathMarkedReserve n (familyEpsilon n)) ∧
    Tendsto
      (fun n : ℕ => familyRatio n / ((n : ℝ) / 4))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto familyRatio atTop atTop ∧
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      familyArea n ≤ C * familyReserve n

end

end MathlibPlus.Open.ResearchFormalization
