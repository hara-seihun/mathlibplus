import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.RankFourFan

/-- The integer representatives `0, ..., 15` of the four-dimensional binary quotient. -/
abbrev Quotient := Fin 16

/-- The lower and upper halves of the quotient and the eight fixed-displacement lines. -/
def H : Finset Quotient := Finset.univ.filter (fun r => r.val < 8)

def low (t : Fin 8) : Quotient := ⟨t.val, by omega⟩

def high (t : Fin 8) : Quotient := ⟨t.val + 8, by omega⟩

def L (t : Fin 8) : Finset Quotient := {low t, high t}

def S (t : Fin 8) : Finset Quotient := H ∪ {high t}

/-- Addition by the common displacement `8`. -/
def translate8 (r : Quotient) : Quotient :=
  ⟨if r.val < 8 then r.val + 8 else r.val - 8, by split <;> omega⟩

def translateSet8 (A : Finset Quotient) : Finset Quotient := A.image translate8

/-- Binary translation on the integer representatives. -/
def xor4 (a b : Quotient) : Quotient :=
  ⟨Nat.xor a.val b.val % 16, Nat.mod_lt _ (by norm_num)⟩

def trivialTranslationStabilizer (A : Finset Quotient) : Prop :=
  ∀ u : Quotient,
    (∀ r : Quotient, xor4 u r ∈ A ↔ r ∈ A) →
      u = (0 : Quotient)

def linePartition : Prop :=
  ∀ r : Quotient, ∃! t : Fin 8, r ∈ L t

def fanSetFacts : Prop :=
  (∀ t : Fin 8,
    (S t).card = 9 ∧
    trivialTranslationStabilizer (S t) ∧
    (S t ∩ translateSet8 (S t)) = L t) ∧
  linePartition

abbrev Vertex (n : Nat) := Fin n → Bool

def coordinate (n k : Nat) (hk : k < n) : Fin n := ⟨k, hk⟩

def boolToNat (b : Bool) : Nat := if b then 1 else 0

def boolNot (b : Bool) : Bool := if b then false else true

def boolXor (a b : Bool) : Bool := if a = b then false else true

def flipVertex {n : Nat} (i : Fin n) (x : Vertex n) : Vertex n :=
  fun k => if k = i then boolNot (x k) else x k

def translateVertex {n : Nat} (a x : Vertex n) : Vertex n :=
  fun k => boolXor (a k) (x k)

/-- The quotient map `F_i` from the claim, with the binary quotient written modulo `16`. -/
def heavyRaw (n : Nat) (hn : 12 ≤ n) (i : Fin 8) (x : Vertex n) : Nat :=
  (∑ a : Fin 4,
      2 ^ a.val * boolToNat (x (coordinate n (8 + a.val) (by omega)))) +
    8 * ∑ j : Fin 8,
      if j = i then 0
      else boolToNat (x (coordinate n j.val (by omega)))

def heavyQuotient (n : Nat) (hn : 12 ≤ n) (i : Fin 8) (x : Vertex n) : Quotient :=
  ⟨heavyRaw n hn i x % 16, Nat.mod_lt _ (by norm_num)⟩

def heavyFunction (n : Nat) (hn : 12 ≤ n) (i : Fin 8) (x : Vertex n) : Bool :=
  if heavyQuotient n hn i x ∈ S i then true else false

def parityRaw (n : Nat) (j : Fin n) (x : Vertex n) : Nat :=
  ∑ k : Fin n, if k = j then 0 else boolToNat (x k)

def tailFunction (n : Nat) (j : Fin n) (x : Vertex n) : Bool :=
  if parityRaw n j x % 2 = 0 then true else false

def translationOrbit {n : Nat} (f : Vertex n → Bool) : Finset (Vertex n → Bool) :=
  (Finset.univ : Finset (Vertex n)).image (fun a => fun x => f (translateVertex a x))

def heavyDensityCount (n : Nat) (hn : 12 ≤ n) (i : Fin 8) : Nat :=
  (Finset.univ : Finset (Vertex n)).filter
    (fun x => heavyFunction n hn i x = true) |>.card

def tailDensityCount (n : Nat) (j : Fin n) : Nat :=
  (Finset.univ : Finset (Vertex n)).filter
    (fun x => tailFunction n j x = true) |>.card

def rankFourFanFacts (n : Nat) (hn : 12 ≤ n) : Prop :=
  fanSetFacts ∧
  (∀ i : Fin 8, Function.Surjective (heavyQuotient n hn i)) ∧
  (∀ i : Fin 8,
    (translationOrbit (heavyFunction n hn i)).card = 16 ∧
    16 * heavyDensityCount n hn i = 9 * 2 ^ n) ∧
  (∀ j : Fin n, 8 ≤ j.val →
    (translationOrbit (tailFunction n j)).card = 2 ∧
    2 * tailDensityCount n j = 2 ^ n)

/-- Claim 31337: the rank-four fixed-displacement fan construction and its stated
stabilizer, orbit, and density data. -/
def claim31337 : Prop :=
  ∀ (n : Nat) (hn : 12 ≤ n), rankFourFanFacts n hn

/-- The opposite-pair event in direction `i` for a square using distinct heavy
 directions `i` and `j`. -/
def heavyOppositePair
    (n : Nat) (hn : 12 ≤ n) (i j : Fin 8) (x : Vertex n) : Prop :=
  heavyQuotient n hn i x ∈ L i

/-- The four selected edges of a coordinate square in two heavy directions. -/
def heavyHeavySquare
    (n : Nat) (hn : 12 ≤ n) (i j : Fin 8) (x : Vertex n) : Prop :=
  heavyFunction n hn i x = true ∧
  heavyFunction n hn j x = true ∧
  heavyFunction n hn i (flipVertex (coordinate n j.val (by omega)) x) = true ∧
  heavyFunction n hn j (flipVertex (coordinate n i.val (by omega)) x) = true

/-- Claim 31338: translation by `8` turns each other-direction quotient into
its opposite, the two opposite-pair events are disjoint, and no heavy-heavy
coordinate square is complete. -/
def claim31338 : Prop :=
  ∀ (n : Nat) (hn : 12 ≤ n),
    ∀ i j : Fin 8, i ≠ j →
      (∀ x : Vertex n,
        heavyQuotient n hn i
            (flipVertex (coordinate n j.val (by omega)) x) =
          translate8 (heavyQuotient n hn i x) ∧
        heavyQuotient n hn j
            (flipVertex (coordinate n i.val (by omega)) x) =
          translate8 (heavyQuotient n hn j x)) ∧
      (∀ x : Vertex n,
        heavyOppositePair n hn i j x ↔
          (heavyFunction n hn i x = true ∧
            heavyFunction n hn i
              (flipVertex (coordinate n j.val (by omega)) x) = true)) ∧
      (∀ x : Vertex n,
        heavyOppositePair n hn j i x ↔
          (heavyFunction n hn j x = true ∧
            heavyFunction n hn j
              (flipVertex (coordinate n i.val (by omega)) x) = true)) ∧
      (∀ x : Vertex n,
        ¬(heavyOppositePair n hn i j x ∧
          heavyOppositePair n hn j i x)) ∧
      (∀ x : Vertex n, ¬heavyHeavySquare n hn i j x)

end MathlibPlus.Open.ResearchFormalization.RankFourFan
