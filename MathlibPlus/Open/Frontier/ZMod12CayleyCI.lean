import Mathlib

namespace MathlibPlus.Open.Frontier

abbrev Z12 := ZMod 12

def p1 : Finset Z12 := {1, 11}
def p2 : Finset Z12 := {2, 10}
def p3 : Finset Z12 := {3, 9}
def p4 : Finset Z12 := {4, 8}
def p5 : Finset Z12 := {5, 7}
def p6 : Finset Z12 := {6}

def pairAt (i : Fin 6) : Finset Z12 :=
  match i.val with
  | 0 => p1
  | 1 => p2
  | 2 => p3
  | 3 => p4
  | 4 => p5
  | _ => p6

def inverseClosed (S : Finset Z12) : Prop :=
  (0 : Z12) ∉ S ∧ ∀ x : Z12, x ∈ S → -x ∈ S

def bitEncoding (S : Finset Z12) : Fin 6 → Bool :=
  fun i => decide (pairAt i ⊆ S)

def hasBitEncoding (S : Finset Z12) (b : Fin 6 → Bool) : Prop :=
  ∀ i : Fin 6, b i = true ↔ pairAt i ⊆ S

def connectionSet (b : Fin 6 → Bool) : Finset Z12 :=
  (if b 0 = true then p1 else ∅) ∪
  (if b 1 = true then p2 else ∅) ∪
  (if b 2 = true then p3 else ∅) ∪
  (if b 3 = true then p4 else ∅) ∪
  (if b 4 = true then p5 else ∅) ∪
  (if b 5 = true then p6 else ∅)

def bits6 (b1 b2 b3 b4 b5 b6 : Bool) : Fin 6 → Bool :=
  fun i =>
    match i.val with
    | 0 => b1
    | 1 => b2
    | 2 => b3
    | 3 => b4
    | 4 => b5
    | _ => b6

def lowBits (b2 b3 b4 b6 : Bool) : Fin 4 → Bool :=
  fun i =>
    match i.val with
    | 0 => b2
    | 1 => b3
    | 2 => b4
    | _ => b6

def bitsFromLow (c : Fin 4 → Bool) (b1 b5 : Bool) : Fin 6 → Bool :=
  fun i =>
    match i.val with
    | 0 => b1
    | 1 => c 0
    | 2 => c 1
    | 3 => c 2
    | 4 => b5
    | _ => c 3

def cayleyAdj (S : Finset Z12) (x y : Z12) : Prop :=
  x ≠ y ∧ x - y ∈ S

def cayleyGraphIsomorphic (S T : Finset Z12) : Prop :=
  ∃ e : Equiv.Perm Z12, ∀ x y : Z12,
    cayleyAdj S x y ↔ cayleyAdj T (e x) (e y)

def unitMultipliers : Finset Z12 := {1, 5, 7, 11}

def unitOrbit (S T : Finset Z12) : Prop :=
  ∃ u : Z12, u ∈ unitMultipliers ∧ T = S.image (fun x => u * x)

def additiveAutomorphismOrbit (S T : Finset Z12) : Prop :=
  ∃ e : AddEquiv Z12 Z12, T = S.image e

def sameFiberBits (S T : Finset Z12) : Prop :=
  bitEncoding S 1 = bitEncoding T 1 ∧
  bitEncoding S 2 = bitEncoding T 2 ∧
  bitEncoding S 3 = bitEncoding T 3 ∧
  bitEncoding S 5 = bitEncoding T 5 ∧
  ((bitEncoding S 0 = bitEncoding T 0 ∧
      bitEncoding S 4 = bitEncoding T 4) ∨
    (bitEncoding S 0 = bitEncoding T 4 ∧
      bitEncoding S 4 = bitEncoding T 0))

def allConnectionSets : Finset (Finset Z12) :=
  (Finset.univ : Finset (Fin 6 → Bool)).image connectionSet

def graphIsoClass (S : Finset Z12) : Set (Finset Z12) :=
  {T | inverseClosed T ∧ cayleyGraphIsomorphic S T}

noncomputable def graphIsoFiber (S : Finset Z12) : Finset (Finset Z12) := by
  classical
  exact (Finset.univ : Finset (Finset Z12)).filter
    (fun T => inverseClosed T ∧ cayleyGraphIsomorphic S T)

def singletonFiberRepresentatives : Finset (Finset Z12) :=
  ((Finset.univ : Finset (Fin 4 → Bool)).image
      (fun c => connectionSet (bitsFromLow c false false))) ∪
    ((Finset.univ : Finset (Fin 4 → Bool)).image
      (fun c => connectionSet (bitsFromLow c true true)))

def doubletonFiberRepresentatives : Finset (Finset Z12) :=
  (Finset.univ : Finset (Fin 4 → Bool)).image
    (fun c => connectionSet (bitsFromLow c false true))

noncomputable def singletonFibers : Finset (Finset (Finset Z12)) :=
  singletonFiberRepresentatives.image graphIsoFiber

noncomputable def doubletonFibers : Finset (Finset (Finset Z12)) :=
  doubletonFiberRepresentatives.image graphIsoFiber

/-- The complete fixed-order classification of inverse-closed connection sets in Z/12Z. -/
def zmod12UndirectedCayleyCI : Prop :=
  (∀ S : Finset Z12, inverseClosed S →
    ∃! b : Fin 6 → Bool, hasBitEncoding S b)
  ∧ (∀ S : Finset Z12, inverseClosed S →
    S = connectionSet (bitEncoding S))
  ∧ (∀ b : Fin 6 → Bool, inverseClosed (connectionSet b))
  ∧ (∀ S : Finset Z12,
    inverseClosed S ↔ S ∈ allConnectionSets)
  ∧ allConnectionSets.card = 64
  ∧ (∀ S T : Finset Z12,
    inverseClosed S → inverseClosed T →
      (cayleyGraphIsomorphic S T ↔ sameFiberBits S T) ∧
      (cayleyGraphIsomorphic S T ↔ unitOrbit S T) ∧
      (unitOrbit S T ↔ additiveAutomorphismOrbit S T))
  ∧ (∀ (b2 b3 b4 b6 : Bool),
    graphIsoClass
        (connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) false false)) =
      ({connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) false false)} :
        Set (Finset Z12)) ∧
    graphIsoClass
        (connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) true true)) =
      ({connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) true true)} :
        Set (Finset Z12)) ∧
    graphIsoClass
        (connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) false true)) =
      ({connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) false true),
        connectionSet (bitsFromLow (lowBits b2 b3 b4 b6) true false)} :
        Set (Finset Z12)))
  ∧ singletonFibers.card = 32
  ∧ doubletonFibers.card = 16
  ∧ singletonFibers.card + doubletonFibers.card = 48
  ∧ (∀ C ∈ singletonFibers, C.card = 1)
  ∧ (∀ C ∈ doubletonFibers, C.card = 2)
  ∧ Disjoint singletonFibers doubletonFibers
  ∧ (∀ S : Finset Z12, inverseClosed S →
      graphIsoFiber S ∈ singletonFibers ∨ graphIsoFiber S ∈ doubletonFibers)

end MathlibPlus.Open.Frontier
