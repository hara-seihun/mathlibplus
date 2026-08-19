import MathlibPlus.Algebra.BinaryCarry
import MathlibPlus.NumberTheory.CarryRecurrence
import MathlibPlus.NumberTheory.WeightedDyadicTail

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.NumberTheory.Claim35661_35666_35672

noncomputable section

/-- The unscaled finite-prefix sum for a binary digit word. -/
def finitePrefix (d : ℕ → ℕ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range k,
    ((j + 1 : ℕ) : ℚ) * (d j : ℚ) / (2 : ℚ) ^ (j + 1)

/-- The scaled residual carry attached to a rational target and prefix. -/
def carryValue (p q k : ℕ) (d : ℕ → ℕ) : ℚ :=
  (q : ℚ) * (2 : ℚ) ^ k *
    ((p : ℚ) / q - finitePrefix d k)

/-- A retained state is a depth and its exact rational carry. -/
def feasibleCarry (q k : ℕ) (r : ℚ) : Prop :=
  0 ≤ r ∧ r ≤ (q : ℚ) * (k + 2 : ℕ)

/-- The two children from the exact carry recurrence. -/
def carryChild (q k : ℕ) (r : ℚ) (b : Bool) : ℚ :=
  if b = false then 2 * r else
    2 * r - (q : ℚ) * (k + 1 : ℕ)

/-- The finite-prefix equality represented by a zero carry. -/
def finitePrefixEquality (p q k : ℕ) (d : ℕ → ℕ) : Prop :=
  (p : ℚ) / q = finitePrefix d k ∧
    ∀ j : ℕ, j < k → d j = 0 ∨ d j = 1

/-- The exact finite-leaf status, including the binary-prefix carrier. -/
def finiteLeaf (p q k : ℕ) (d : ℕ → ℕ) : Prop :=
  finitePrefixEquality p q k d

/-- A nonzero retained state strictly before the horizon with no retained
child.  The strict interior condition is what distinguishes dead from an
unresolved scan frontier. -/
def deadCarryState (q H k : ℕ) (r : ℚ) : Prop :=
  k < H ∧ r ≠ 0 ∧
    ¬ ∃ b : Bool, feasibleCarry q (k + 1) (carryChild q k r b)

/-- A nonzero retained state at the finite scan horizon. -/
def unresolvedHorizonState (q H k : ℕ) (r : ℚ) : Prop :=
  k = H ∧ r ≠ 0

/-- Claim 35661: zero carry is a finite exact leaf; childless nonzero
interior states are dead; nonzero horizon states are unresolved. -/
def claim35661 : Prop :=
  (∀ p q : ℕ, 0 < p → 0 < q → Nat.Coprime p q →
      ∀ d : ℕ → ℕ, (∀ j : ℕ, d j ≤ 1) →
        ∀ k : ℕ, carryValue p q k d = 0 → finiteLeaf p q k d) ∧
  (∀ q H k : ℕ, ∀ r : ℚ,
      0 < q → k < H → r ≠ 0 → feasibleCarry q k r →
        (¬ ∃ b : Bool, feasibleCarry q (k + 1) (carryChild q k r b)) →
          deadCarryState q H k r) ∧
  (∀ q H k : ℕ, ∀ r : ℚ,
      0 < q → k = H → r ≠ 0 → feasibleCarry q k r →
        unresolvedHorizonState q H k r ∧ ¬ deadCarryState q H k r)

/-- Carry after a finite binary word. -/
def carryAlong (q k : ℕ) (r : ℚ) : List Bool → ℚ
  | [] => r
  | b :: w => carryAlong q (k + 1) (carryChild q k r b) w

/-- A path follows only retained children and stops at a zero carry. -/
def feasibleCarryPath (q k : ℕ) (r : ℚ) : List Bool → Prop
  | [] => feasibleCarry q k r
  | b :: w =>
      feasibleCarry q k r ∧ r ≠ 0 ∧
        feasibleCarryPath q (k + 1) (carryChild q k r b) w

/-- The exact budget recurrence with `⊥ : WithBot ℤ` as `-∞`.  A one-child
state inherits its child budget; only a two-child state consumes one complete
binary branch generation. -/
noncomputable def carryBudgetAux (q : ℕ) : ℕ → ℕ → ℚ → WithBot ℤ
  | 0, _k, _r => 0
  | n + 1, k, r =>
      if r = 0 then 0
      else
        let c₀ := carryChild q k r false
        let c₁ := carryChild q k r true
        let f₀ := feasibleCarry q (k + 1) c₀
        let f₁ := feasibleCarry q (k + 1) c₁
        if f₀ then
          if f₁ then
            1 + min (carryBudgetAux q n (k + 1) c₀)
              (carryBudgetAux q n (k + 1) c₁)
          else carryBudgetAux q n (k + 1) c₀
        else if f₁ then
          carryBudgetAux q n (k + 1) c₁
        else ⊥

/-- Budget at a state for a scan horizon `H`. -/
noncomputable def carryBudget (q H k : ℕ) (r : ℚ) : WithBot ℤ :=
  carryBudgetAux q (H - k) k r

/-- The fixed-horizon recurrence stated directly at every retained state. -/
def budgetRecurrence (q H k : ℕ) (r : ℚ) : Prop :=
  k ≤ H →
    carryBudget q H k r =
      if r = 0 then 0
      else if k = H then 0
      else
        let c₀ := carryChild q k r false
        let c₁ := carryChild q k r true
        let f₀ := feasibleCarry q (k + 1) c₀
        let f₁ := feasibleCarry q (k + 1) c₁
        if f₀ then
          if f₁ then
            1 + min (carryBudget q H (k + 1) c₀)
              (carryBudget q H (k + 1) c₁)
          else carryBudget q H (k + 1) c₀
        else if f₁ then
          carryBudget q H (k + 1) c₁
        else ⊥

/-- A state can certify zero generations only when the one-child chains
below it reach a zero leaf or the horizon; a dead interior state therefore
has budget `-∞`, not zero. -/
def usableZeroGeneration (q H : ℕ) : ℕ → ℕ → ℚ → Prop
  | 0, k, r => feasibleCarry q k r ∧ (r = 0 ∨ k = H)
  | fuel + 1, k, r =>
      feasibleCarry q k r ∧
        (r = 0 ∨ k = H ∨
          let c₀ := carryChild q k r false
          let c₁ := carryChild q k r true
          let f₀ := feasibleCarry q (k + 1) c₀
          let f₁ := feasibleCarry q (k + 1) c₁
          ((f₀ ∧ f₁ ∧
              usableZeroGeneration q H fuel (k + 1) c₀ ∧
              usableZeroGeneration q H fuel (k + 1) c₁) ∨
            (f₀ ∧ ¬ f₁ ∧
              usableZeroGeneration q H fuel (k + 1) c₀) ∨
            (¬ f₀ ∧ f₁ ∧
              usableZeroGeneration q H fuel (k + 1) c₁)))

/-- Certified generations use horizon fuel for recursion.  In particular, a
one-child transition recurses with the same generation count, while a
two-child transition decrements it. -/
def certifiedBranchGeneration (q H : ℕ) : ℕ → ℕ → ℕ → ℚ → Prop
  | 0, 0, k, r => usableZeroGeneration q H 0 k r
  | 0, _n + 1, _k, _r => False
  | fuel + 1, 0, k, r => usableZeroGeneration q H (fuel + 1) k r
  | fuel + 1, n + 1, k, r =>
      feasibleCarry q k r ∧ k < H ∧ r ≠ 0 ∧
        let c₀ := carryChild q k r false
        let c₁ := carryChild q k r true
        let f₀ := feasibleCarry q (k + 1) c₀
        let f₁ := feasibleCarry q (k + 1) c₁
        ((f₀ ∧ f₁ ∧
            certifiedBranchGeneration q H fuel n (k + 1) c₀ ∧
            certifiedBranchGeneration q H fuel n (k + 1) c₁) ∨
          (f₀ ∧ ¬ f₁ ∧
            certifiedBranchGeneration q H fuel (n + 1) (k + 1) c₀) ∨
          (¬ f₀ ∧ f₁ ∧
            certifiedBranchGeneration q H fuel (n + 1) (k + 1) c₁))

/-- The largest-generation predicate for a root carry. -/
def largestCertifiedGeneration (q p H b : ℕ) : Prop :=
  b ≤ H ∧ certifiedBranchGeneration q H H b 0 (p : ℚ) ∧
    ∀ n : ℕ, b < n → n ≤ H →
      ¬ certifiedBranchGeneration q H H n 0 (p : ℚ)

/-- Claim 35666: the exact fixed-horizon budget recurrence and its root
interpretation as the largest number of complete binary branch generations. -/
def claim35666 : Prop :=
  (∀ q H k : ℕ, ∀ r : ℚ,
      0 < q → k ≤ H → feasibleCarry q k r → budgetRecurrence q H k r) ∧
  (∀ p q H : ℕ,
      0 < q → feasibleCarry q 0 (p : ℚ) →
        ∃ b : ℕ,
          carryBudget q H 0 (p : ℚ) = (b : ℤ) ∧
            largestCertifiedGeneration q p H b)

/-- The universal algebraic recurrence for every rational target and finite
binary prefix. -/
def exactRationalRecurrence : Prop :=
  ∀ X q : ℚ, ∀ d : ℕ → ℕ, (∀ j : ℕ, d j ≤ 1) → ∀ k : ℕ,
    let r : ℕ → ℚ := fun n =>
      q * (2 : ℚ) ^ n * (X - finitePrefix d n)
    r (k + 1) = 2 * r k - q * (k + 1 : ℕ) * d k

/-- The exact reduced target and finite-scan scope. -/
def finiteScanScope (p q H : ℕ) : Prop :=
  0 < p ∧ 0 < q ∧ Nat.Coprime p q ∧
    0 < (p : ℚ) / q ∧ (p : ℚ) / q ≤ 2 ∧
    q ≤ 100 ∧ H ≤ 3000

/-- The retained children of a nonzero state. -/
noncomputable def retainedChildren (q k : ℕ) (r : ℚ) : Finset (ℕ × ℚ) :=
  if r = 0 then ∅ else
    let c₀ := carryChild q k r false
    let c₁ := carryChild q k r true
    (if feasibleCarry q (k + 1) c₀ then {(k + 1, c₀)} else ∅) ∪
      (if feasibleCarry q (k + 1) c₁ then {(k + 1, c₁)} else ∅)

/-- Exact finite scan nodes.  Zero-carry states are inserted as terminal
leaves and are never expanded by a later scan step. -/
noncomputable def finiteScanNodes (q p : ℕ) : ℕ → Finset (ℕ × ℚ)
  | 0 => {(0, (p : ℚ))}
  | n + 1 =>
      let previous := finiteScanNodes q p n
      let frontier := previous.filter (fun s => s.1 = n ∧ s.2 ≠ 0)
      previous ∪ frontier.biUnion (fun s => retainedChildren q n s.2)

/-- The path semantics of the finite scan. -/
def scanPathMembership (q p k : ℕ) (r : ℚ) : Prop :=
  ∃ w : List Bool,
    w.length = k ∧
      feasibleCarryPath q 0 (p : ℚ) w ∧
        carryAlong q 0 (p : ℚ) w = r

/-- Exactness and exhaustiveness of the finite scan through its declared
horizon. -/
def finiteScanExact (q p H : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ H → ∀ r : ℚ,
    (k, r) ∈ finiteScanNodes q p H ↔ scanPathMembership q p k r

/-- A nonzero scan state at the horizon is an unresolved frontier. -/
def finiteScanFrontier (p q H k : ℕ) (r : ℚ) : Prop :=
  finiteScanScope p q H ∧ k = H ∧ r ≠ 0 ∧ feasibleCarry q k r

/-- Claim 35672: the recurrence is universal; exact finite propagation is
scoped to reduced `0 < p/q ≤ 2`, `q ≤ 100`, `H ≤ 3000`; nonzero horizon
states remain unresolved rather than dead. -/
def claim35672 : Prop :=
  exactRationalRecurrence ∧
    (∀ p q H : ℕ, finiteScanScope p q H →
      finiteScanExact q p H ∧
        ∀ k : ℕ, ∀ r : ℚ,
          finiteScanFrontier p q H k r →
            unresolvedHorizonState q H k r ∧
              ¬ deadCarryState q H k r)

end
end MathlibPlus.Open.NumberTheory.Claim35661_35666_35672
