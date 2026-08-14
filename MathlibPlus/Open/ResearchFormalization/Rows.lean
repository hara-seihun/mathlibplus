import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-! Lexicographic signatures and weak orders for finite stacks of real-valued rows. -/

def stackSignature {S : Type*} {n : Nat} (r : Fin (n + 1) → S → ℝ) (e : S) : Fin (n + 1) → ℝ :=
  fun j => r j e

def lexLess {n : Nat} (a b : Fin (n + 1) → ℝ) : Prop :=
  ∃ j : Fin (n + 1),
    (∀ i : Fin (n + 1), i < j → a i = b i) ∧ a j < b j

def lexLE {n : Nat} (a b : Fin (n + 1) → ℝ) : Prop :=
  a = b ∨ lexLess a b

def rowValue {S : Type*} {n : Nat} (N : Fin (n + 1) → ℕ)
    (r : Fin (n + 1) → S → ℝ) (e : S) : ℝ :=
  ∑ j : Fin (n + 1), (N j : ℝ) * r j e

def singleWeakOrder {S : Type*} (r : S → ℝ) : S → S → Prop :=
  fun e f => r e ≤ r f

def stackWeakOrder {S : Type*} {n : Nat} (r : Fin (n + 1) → S → ℝ) : S → S → Prop :=
  fun e f => lexLE (stackSignature r e) (stackSignature r f)

def firstDifferencePairs {S : Type*} {n : Nat} (r : Fin (n + 1) → S → ℝ)
    (j : Fin (n + 1)) : Set (S × S) :=
  {p | (∀ i : Fin (n + 1), i < j → r i p.1 = r i p.2) ∧ r j p.1 ≠ r j p.2}

def rowDifference {S : Type*} {n : Nat} (r : Fin (n + 1) → S → ℝ)
    (j : Fin (n + 1)) (e f : S) : ℝ :=
  r j e - r j f

def laterContribution {S : Type*} {n : Nat} (N : Fin (n + 1) → ℕ)
    (r : Fin (n + 1) → S → ℝ) (j : Fin (n + 1)) (e f : S) : ℝ :=
  Finset.sum (Finset.univ.filter (fun i : Fin (n + 1) => j < i))
    (fun i => (N i : ℝ) * rowDifference r i e f)

def differenceMagnitudes {S : Type*} {n : Nat} (r : Fin (n + 1) → S → ℝ)
    (j : Fin (n + 1)) : Set ℝ :=
  {x | ∃ e f : S, (e, f) ∈ firstDifferencePairs r j ∧ x = |rowDifference r j e f|}

def laterMagnitudes {S : Type*} {n : Nat} (N : Fin (n + 1) → ℕ)
    (r : Fin (n + 1) → S → ℝ) (j : Fin (n + 1)) : Set ℝ :=
  {x | ∃ e f : S, (e, f) ∈ firstDifferencePairs r j ∧
    x = |laterContribution N r j e f|}

/-- The additive-family and signature data in Statement 1. -/
def claim51584 : Prop :=
  ∀ (S : Type*) (_ : Fintype S) (A : AddSubmonoid (S → ℝ)) (n : Nat)
    (r : Fin (n + 1) → S → ℝ),
    (∀ j, r j ∈ A) →
    ∀ e : S, stackSignature r e = fun j => r j e

/-- The first-difference pairs are precisely the pairs first separated at `j`. -/
def claim51587 : Prop :=
  ∀ (S : Type*) (_ : Fintype S) (n : Nat)
    (r : Fin (n + 1) → S → ℝ) (j : Fin (n + 1)) (e f : S),
    (e, f) ∈ firstDifferencePairs r j ↔
      ((∀ i : Fin (n + 1), i < j → r i e = r i f) ∧ r j e ≠ r j f)

/-- Backward coefficients, including the minimum-gap and later-contribution clauses. -/
def canonicalCoefficients {S : Type*} {n : Nat} [Fintype S]
    (r : Fin (n + 1) → S → ℝ) (N : Fin (n + 1) → ℕ) : Prop :=
  (∀ j, 0 < N j) ∧
    N (Fin.last n) = 1 ∧
    ∀ j : Fin (n + 1),
      (firstDifferencePairs r j = ∅ → N j = 1) ∧
      (firstDifferencePairs r j ≠ ∅ →
        ∃ δ B : ℝ,
          0 < δ ∧
          IsLeast (differenceMagnitudes r j) δ ∧
          IsGreatest (laterMagnitudes N r j) B ∧
          N j = ⌊B / δ⌋₊ + 1 ∧
          (N j : ℝ) * δ > B)

/-- Every finite stack admits the stated backwards coefficient choice. -/
def claim51588 : Prop :=
  ∀ (S : Type*) (_ : Fintype S) (n : Nat)
    (r : Fin (n + 1) → S → ℝ),
    ∃ N : Fin (n + 1) → ℕ, canonicalCoefficients r N

/-- The aggregate row belongs to the additive family and preserves strict order and ties. -/
def claim51590 : Prop :=
  ∀ (S : Type*) (_ : Fintype S) (A : AddSubmonoid (S → ℝ)) (n : Nat)
    (r : Fin (n + 1) → S → ℝ) (N : Fin (n + 1) → ℕ),
    (∀ j, r j ∈ A) → canonicalCoefficients r N →
      (fun e => rowValue N r e) ∈ A ∧
      ∀ e f : S,
        (lexLess (stackSignature r e) (stackSignature r f) ↔
          rowValue N r e < rowValue N r f) ∧
        (stackSignature r e = stackSignature r f ↔
          rowValue N r e = rowValue N r f)

def stackOrders {S : Type*} [Fintype S] (A : AddSubmonoid (S → ℝ)) :
    Set (S → S → Prop) :=
  {o | ∃ (n : Nat) (r : Fin (n + 1) → S → ℝ),
    (∀ j, r j ∈ A) ∧ o = stackWeakOrder r}

def singleOrders {S : Type*} [Fintype S] (A : AddSubmonoid (S → ℝ)) :
    Set (S → S → Prop) :=
  {o | ∃ r : S → ℝ, r ∈ A ∧ o = singleWeakOrder r}

/-- Finite stacks and single additive rows obtain exactly the same weak orders. -/
def claim51592 : Prop :=
  ∀ (S : Type*) (_ : Fintype S) (A : AddSubmonoid (S → ℝ)),
    stackOrders A = singleOrders A

end MathlibPlus.Open.ResearchFormalization
