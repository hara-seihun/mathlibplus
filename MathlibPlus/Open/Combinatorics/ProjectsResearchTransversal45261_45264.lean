import Mathlib

open scoped BigOperators Classical
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

/-! The exact 100-by-200 transversal family.  A member is represented by its
chosen point in every block. -/

def transversalMember45262 (s : Fin 100 → Fin 200) : Finset (Fin 100 × Fin 200) :=
  Finset.univ.image (fun r => (r, s r))

def transversalFamily45262 : Finset (Finset (Fin 100 × Fin 200)) :=
  Finset.univ.image transversalMember45262

def selectedBlocks45262
    (S : Finset (Fin 100 × Fin 200)) : Finset (Fin 100) :=
  S.image Prod.fst

def isPartialTransversal45262
    (S : Finset (Fin 100 × Fin 200)) : Prop :=
  ∀ r : Fin 100, (S.filter (fun p => p.1 = r)).card ≤ 1

def transversalLink45262
    (S : Finset (Fin 100 × Fin 200)) : Finset (Finset (Fin 100 × Fin 200)) :=
  transversalFamily45262.filter (fun A => S ⊆ A)

def linkFraction45262 (S : Finset (Fin 100 × Fin 200)) : ℚ :=
  ((transversalLink45262 S).card : ℚ) /
    (transversalFamily45262.card : ℚ)

def distinctBlockCount45262 (S : Finset (Fin 100 × Fin 200)) : ℕ :=
  (selectedBlocks45262 S).card

/-- Claim R-2826.2 (45262). -/
def claim45262 : Prop :=
  transversalFamily45262.card = 200 ^ 100 ∧
    (∀ S : Finset (Fin 100 × Fin 200),
      isPartialTransversal45262 S →
        linkFraction45262 S =
          (1 : ℚ) / 200 ^ distinctBlockCount45262 S) ∧
    (∀ S : Finset (Fin 100 × Fin 200),
      ¬ isPartialTransversal45262 S →
        transversalLink45262 S = ∅) ∧
    (∀ S : Finset (Fin 100 × Fin 200), S.Nonempty →
      linkFraction45262 S <
        (1 : ℚ) / 100 ^ S.card)

/-! Ordered intersection classes of two transversals. -/

def transversalIntersectionSize45263
    (A B : Finset (Fin 100 × Fin 200)) : ℕ :=
  (A ∩ B).card

def intersectionClass45263 (j : ℕ) : Finset
    (Finset (Fin 100 × Fin 200) × Finset (Fin 100 × Fin 200)) :=
  (transversalFamily45262.product transversalFamily45262).filter
    (fun p => transversalIntersectionSize45263 p.1 p.2 = j)

def p45263 (j : ℕ) : ℚ :=
  (Nat.choose 100 j : ℚ) * 200 ^ 100 * 199 ^ (100 - j) /
    (200 ^ 100 : ℚ) ^ 2

/-- Claim R-2826.3 (45263). -/
def claim45263 : Prop :=
  (∀ j : ℕ,
    (intersectionClass45263 j).card =
      Nat.choose 100 j * 200 ^ 100 * 199 ^ (100 - j)) ∧
    (∀ j : ℕ,
      p45263 j =
        (Nat.choose 100 j : ℚ) * 199 ^ (100 - j) / 200 ^ 100) ∧
    p45263 11 > (1 : ℚ) / 10 ^ 12 ∧
    p45263 12 ≤ (1 : ℚ) / 10 ^ 12 ∧
    (∀ j ≥ 12, p45263 j ≤ p45263 12)

/-- The finite truncated sequence factor from the audited Case 3
calculation. -/
def H45264 (r s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s + 1), Nat.choose r i * i.factorial

def R45264 : ℚ :=
  p45263 12 / p45263 11 * (H45264 12 11 : ℚ) / H45264 11 11

/-- Claim R-2826.4 (45264). -/
def claim45264 : Prop :=
  R45264 = (73252317305 : ℚ) / 259110207456 ∧
    R45264 > (256 : ℚ) / 244140625 ∧
    R45264 > 2 ^ 20 * (1 : ℚ) / 10 ^ 12 ∧
    p45263 12 / p45263 11 = (89 : ℚ) / 2388 ∧
    0 < (H45264 12 11 : ℚ) / H45264 11 11

/-- Claim R-2826.1 (45261), as the exact logical audit: the two frequency
inequalities alone do not entail the ratio estimate used by the proof. -/
def claim45261 : Prop :=
  ¬ ∀ (a b : ℚ),
      a ≤ (1 : ℚ) / 10 ^ 12 →
      b > (1 : ℚ) / 10 ^ 12 →
      a / b < (1 : ℚ) / 10 ^ 12

end MathlibPlus.Open.ProjectsResearch
