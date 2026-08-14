import Mathlib

namespace MathlibPlus.Open.DecisionTree.Cost

/-- The two signs used for the Boolean values in the packet's Rademacher cube. -/
inductive Sign where
  | neg
  | pos
  deriving DecidableEq, Repr

instance : Fintype Sign where
  elems := {.neg, .pos}
  complete := by
    intro s
    cases s <;> simp

def signValue : Sign → ℚ
  | .neg => -1
  | .pos => 1

abbrev Atom (n : Nat) := (Fin n → Sign) → Sign

/-- Insert a queried sign at coordinate `i`, preserving the order of the other coordinates. -/
def insertAt : {n : Nat} → Fin (n + 1) → Sign → (Fin n → Sign) → (Fin (n + 1) → Sign)
  | 0, _, b, _ => fun _ => b
  | n + 1, ⟨0, _⟩, b, x =>
      fun j => Fin.cases b (fun k => x k) j
  | n + 1, ⟨i + 1, hi⟩, b, x =>
      fun j =>
        Fin.cases (x 0)
          (fun k =>
            insertAt (n := n)
              ⟨i, Nat.lt_of_succ_lt_succ hi⟩ b (fun l => x l.succ) k) j

def restrict {n : Nat} (h : Atom (n + 1)) (i : Fin (n + 1)) (b : Sign) : Atom n :=
  fun x => h (insertAt i b x)

def IsConstant {n : Nat} (h : Atom n) : Prop :=
  ∃ v : Sign, ∀ x, h x = v

/-- Exact Bellman definition of minimum expected deterministic query cost. -/
noncomputable def queryCost : (n : Nat) → Atom n → ℚ
  | 0, _ => 0
  | n + 1, h => by
      classical
      exact
        if IsConstant h then
          0
        else
          1 +
            (Finset.univ : Finset (Fin (n + 1))).inf'
              (by simp)
              (fun i =>
                (queryCost n (restrict h i .neg) +
                  queryCost n (restrict h i .pos)) / 2)

/-- The saving obtained by exposing coordinate `i` first. -/
noncomputable def saving {n : Nat} (h : Atom (n + 1)) (i : Fin (n + 1)) : ℚ :=
  queryCost (n + 1) h -
    (queryCost n (restrict h i .neg) + queryCost n (restrict h i .pos)) / 2

/-- The concrete finite truth-table index, with coordinate zero the low bit. -/
def truthIndex : (n : Nat) → (Fin n → Sign) → Fin (2 ^ n)
  | 0, _ => ⟨0, by simp⟩
  | n + 1, x =>
      let tail := truthIndex n (fun i => x i.succ)
      if x 0 = .pos then
        ⟨2 * (tail : Nat) + 1, by
          have ht := tail.isLt
          simp [Nat.pow_succ]
          omega⟩
      else
        ⟨2 * (tail : Nat), by
          have ht := tail.isLt
          simp [Nat.pow_succ]
          omega⟩

 def h69Table : Fin (2 ^ 3) → Sign :=
  ![.pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg]

 def h197Table : Fin (2 ^ 3) → Sign :=
  ![.pos, .neg, .pos, .neg, .neg, .neg, .pos, .pos]

 def h69 : Atom 3 := fun x => h69Table (truthIndex 3 x)

 def h197 : Atom 3 := fun x => h197Table (truthIndex 3 x)

def rationalValue (h : Atom 3) : (Fin 3 → Sign) → ℚ :=
  fun x => signValue (h x)

def g : (Fin 3 → Sign) → ℚ :=
  fun x =>
    (5 / 11 : ℚ) * rationalValue h69 x +
      (6 / 11 : ℚ) * rationalValue h197 x

def uniformVariance3 (f : (Fin 3 → Sign) → ℚ) : ℚ :=
  let μ : ℚ := (∑ x : Fin 3 → Sign, f x) / 8
  (∑ x : Fin 3 → Sign, (f x - μ) ^ 2) / 8

noncomputable def qDrop (h : Atom 3) (i : Fin 3) : ℚ :=
  saving h i

noncomputable def averagedDrop (i : Fin 3) : ℚ :=
  (5 / 11 : ℚ) * qDrop h69 i + (6 / 11 : ℚ) * qDrop h197 i

def expectedDrops : Fin 3 → ℚ :=
  ![8 / 11, 1 / 2, 17 / 22]

/-- The exact three-coordinate mixture and all of its reported rational checks. -/
def ExactQDropWitness : Prop :=
  uniformVariance3 g = 1671 / 1936 ∧
    (∀ i : Fin 3, averagedDrop i = expectedDrops i) ∧
    (∀ i : Fin 3, averagedDrop i < uniformVariance3 g) ∧
    (∀ i : Fin 3, averagedDrop i ≤ 17 / 22) ∧
    (∃ i : Fin 3, averagedDrop i = 17 / 22) ∧
    uniformVariance3 g - (17 / 22 : ℚ) = 175 / 1936

end MathlibPlus.Open.DecisionTree.Cost
