import Mathlib

namespace MathlibPlus.Open.IndependenceBatch

open scoped BigOperators Polynomial
open Classical

noncomputable section

/-- The vertices of the tree with a leaves at its left endpoint and b leaves at
its right endpoint.  The three `Fin 3` vertices are u, v, and w, in that
order; the two other summands are the pendant leaves. -/
abbrev QVertex (a b : ℕ) := Fin 3 ⊕ (Fin a ⊕ Fin b)

/-- Adjacency in the once-subdivided double star Q_{a,b}. -/
def QAdj (a b : ℕ) : QVertex a b → QVertex a b → Prop
  | Sum.inl i, Sum.inl j =>
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
  | Sum.inl i, Sum.inr (Sum.inl _) => i = 0
  | Sum.inr (Sum.inl _), Sum.inl i => i = 0
  | Sum.inl i, Sum.inr (Sum.inr _) => i = 2
  | Sum.inr (Sum.inr _), Sum.inl i => i = 2
  | Sum.inr _, Sum.inr _ => False

/-- A finite subset is independent when it contains no adjacent pair. -/
def QIndependent (a b : ℕ) (s : Finset (QVertex a b)) : Prop :=
  ∀ ⦃x y : QVertex a b⦄, x ∈ s → y ∈ s → ¬ QAdj a b x y

/-- The independence polynomial obtained by summing x^{|S|} over independent
subsets S of Q_{a,b}. -/
noncomputable def QIndependencePolynomial (a b : ℕ) : ℕ[X] :=
  (Finset.powerset (Finset.univ : Finset (QVertex a b))).sum
    (fun s => if QIndependent a b s then Polynomial.X ^ s.card else 0)

noncomputable def QCoefficient (a b k : ℕ) : ℕ :=
  (QIndependencePolynomial a b).coeff k

def QBinomialPred (n k : ℕ) : ℕ :=
  if k = 0 then 0 else n.choose (k - 1)

def QLogConcave (P : ℕ[X]) : Prop :=
  ∀ k : ℕ, 0 < k →
    P.coeff (k - 1) * P.coeff (k + 1) ≤ P.coeff k * P.coeff k

def QNoInternalZeros (P : ℕ[X]) : Prop :=
  ∀ i j k : ℕ, i < j → j < k →
    P.coeff i ≠ 0 → P.coeff k ≠ 0 → P.coeff j ≠ 0

def QUnimodal (P : ℕ[X]) : Prop :=
  ∃ m : ℕ,
    (∀ i j : ℕ, i ≤ j → j ≤ m → P.coeff i ≤ P.coeff j) ∧
    (∀ i j : ℕ, m ≤ i → i ≤ j → P.coeff j ≤ P.coeff i)

def QabIndependenceFormula (a b : ℕ) : Prop :=
  QIndependencePolynomial a b =
    ((1 + Polynomial.X) ^ a + Polynomial.X) *
        ((1 + Polynomial.X) ^ b + Polynomial.X) +
      Polynomial.X * (1 + Polynomial.X) ^ (a + b)

def QabExpandedFormula (a b : ℕ) : Prop :=
  let n := a + b + 1
  QIndependencePolynomial a b =
    (1 + Polynomial.X) ^ n + Polynomial.X * (1 + Polynomial.X) ^ a +
      Polynomial.X * (1 + Polynomial.X) ^ b + Polynomial.X ^ 2

def QabCoefficientFormula (a b : ℕ) : Prop :=
  ∀ k : ℕ,
    QCoefficient a b k =
      (a + b + 1).choose k + QBinomialPred a k +
        QBinomialPred b k + (if k = 2 then 1 else 0)

def QabClaim60889 (a b : ℕ) : Prop :=
  QabIndependenceFormula a b ∧
    QabExpandedFormula a b ∧
    QabCoefficientFormula a b ∧
    QLogConcave (QIndependencePolynomial a b) ∧
    QNoInternalZeros (QIndependencePolynomial a b)

noncomputable def QForestPolynomial (components : List (ℕ × ℕ)) : ℕ[X] :=
  (components.map (fun p => QIndependencePolynomial p.1 p.2)).prod

def QForestClaim60820 : Prop :=
  (∀ a b : ℕ,
    QLogConcave (QIndependencePolynomial a b) ∧
      QNoInternalZeros (QIndependencePolynomial a b)) ∧
  (∀ components : List (ℕ × ℕ),
    QLogConcave (QForestPolynomial components) ∧
      QUnimodal (QForestPolynomial components))

end

end MathlibPlus.Open.IndependenceBatch
