import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

abbrev Poly := Polynomial ℚ

def b : Poly := Polynomial.X

def natC (n : ℕ) : Poly := Polynomial.C (n : ℚ)

def nonnegativeCoefficients (p : Poly) : Prop :=
  ∀ i : ℕ, 0 ≤ p.coeff i

def rising (z : Poly) (k : ℕ) : Poly :=
  Finset.prod (Finset.range k) (fun i => z + natC i)

def Y (d : ℕ) : Poly := natC 2 * b + natC (d + 1)

def rankFactor (s q : ℕ) : Poly := natC 2 * b + natC (s + q + 1)

def principalProduct (d : ℕ) : Poly :=
  Finset.prod (Finset.range (d + 1)) (fun s =>
    Finset.prod (Finset.range (d + 1)) (fun q =>
      if s < q then rankFactor s q else 1))

def P (d : ℕ) : Poly := natC (Nat.factorial d) * principalProduct d

def delta (d n m l : ℕ) : Poly :=
  rising (Y d) n * rising (Y d - natC 1) m * rising (Y d - natC 2) l

def validRankPair (d : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ p.2 ≤ d

def threeLegAssignment (d n m l : ℕ) : Fin l ⊕ (Fin m ⊕ Fin n) → ℕ × ℕ
  | Sum.inl j => (j.1, d - 2)
  | Sum.inr (Sum.inl j) => (j.1, d - 1)
  | Sum.inr (Sum.inr j) => (j.1, d)

def threeLegFactor (d n m l : ℕ) : Fin l ⊕ (Fin m ⊕ Fin n) → Poly
  | Sum.inl j => Y d - natC 2 + natC j.1
  | Sum.inr (Sum.inl j) => Y d - natC 1 + natC j.1
  | Sum.inr (Sum.inr j) => Y d + natC j.1

def bottomOneDelta (d m n : ℕ) : Poly :=
  rising (Y d) n * rising (Y d - natC 1) m * rising (Y d - natC 2) 1

def bottomOneAssignment (d m n : ℕ) : Unit ⊕ (Fin m ⊕ Fin n) → ℕ × ℕ
  | Sum.inl _ => (0, d - 2)
  | Sum.inr (Sum.inl j) => (j.1, d - 1)
  | Sum.inr (Sum.inr j) => (j.1, d)

def bottomOneFactor (d m n : ℕ) : Unit ⊕ (Fin m ⊕ Fin n) → Poly
  | Sum.inl _ => Y d - natC 2
  | Sum.inr (Sum.inl j) => Y d - natC 1 + natC j.1
  | Sum.inr (Sum.inr j) => Y d + natC j.1

/-- Claim 2092: the three content strings occupy distinct principal factors,
with a coefficientwise nonnegative cleared quotient. -/
def claim_2092 : Prop :=
  ∀ d n m l : ℕ,
    l ≤ d - 2 → m ≤ d - 1 → n ≤ d →
      (∀ i, validRankPair d (threeLegAssignment d n m l i)) ∧
      Function.Injective (threeLegAssignment d n m l) ∧
      (∀ i, threeLegFactor d n m l i =
        rankFactor (threeLegAssignment d n m l i).1
          (threeLegAssignment d n m l i).2) ∧
      delta d n m l ∣ P d ∧
      nonnegativeCoefficients (P d / delta d n m l)

/-- Claim 2107: the bottom-one content string occupies distinct principal
factors, with a coefficientwise nonnegative cleared quotient. -/
def claim_2107 : Prop :=
  ∀ d m n : ℕ,
    m ≤ d - 1 → n ≤ d →
      (∀ i, validRankPair d (bottomOneAssignment d m n i)) ∧
      Function.Injective (bottomOneAssignment d m n) ∧
      (∀ i, bottomOneFactor d m n i =
        rankFactor (bottomOneAssignment d m n i).1
          (bottomOneAssignment d m n i).2) ∧
      bottomOneDelta d m n ∣ P d ∧
      nonnegativeCoefficients (P d / bottomOneDelta d m n)

end

end MathlibPlus.Open.Research
