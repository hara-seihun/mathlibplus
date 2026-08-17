import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19822

open scoped BigOperators Classical

noncomputable section

abbrev SpiderPolynomial := MvPolynomial (Fin 2) ℤ

def u : SpiderPolynomial := MvPolynomial.X 0

def v : SpiderPolynomial := MvPolynomial.X 1

structure DoubleSpider where
  A : Multiset ℕ
  c : ℕ
  B : Multiset ℕ

abbrev LegOccurrence (A : Multiset ℕ) :=
  Σ a : {n : ℕ // n ∈ A}, Fin (A.count a.1)

def occurrenceLength {A : Multiset ℕ} (o : LegOccurrence A) : ℕ :=
  o.1.1

abbrev LegVertex (A : Multiset ℕ) :=
  Σ o : LegOccurrence A, Fin (occurrenceLength o)

abbrev DoubleSpiderVertex (T : DoubleSpider) :=
  Fin (T.c + 1) ⊕ (LegVertex T.A ⊕ LegVertex T.B)

def legAdj {A : Multiset ℕ} (a b : LegVertex A) : Prop :=
  a.1 = b.1 ∧
    (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)

def doubleSpiderAdj (T : DoubleSpider) :
    DoubleSpiderVertex T → DoubleSpiderVertex T → Prop
  | Sum.inl i, Sum.inl j =>
      i.val + 1 = j.val ∨ j.val + 1 = i.val
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => legAdj a b
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => legAdj a b
  | Sum.inl i, Sum.inr (Sum.inl a) => i.val = 0 ∧ a.2.val = 0
  | Sum.inr (Sum.inl a), Sum.inl i => i.val = 0 ∧ a.2.val = 0
  | Sum.inl i, Sum.inr (Sum.inr b) => i.val = T.c ∧ b.2.val = 0
  | Sum.inr (Sum.inr b), Sum.inl i => i.val = T.c ∧ b.2.val = 0
  | _, _ => False

def positiveLegLengths (A : Multiset ℕ) : Prop :=
  ∀ a, a ∈ A → 0 < a

def admissibleDoubleSpider (T : DoubleSpider) : Prop :=
  positiveLegLengths T.A ∧
    positiveLegLengths T.B ∧
    0 < T.c ∧
    2 ≤ T.A.card ∧
    2 ≤ T.B.card

def connectedWithin {α : Type} (r : α → α → Prop)
    (S : Finset α) : Prop :=
  ∀ ⦃a b⦄, a ∈ S → b ∈ S →
    Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ r x y) a b

def connectedVertexSet (T : DoubleSpider)
    (S : Finset (DoubleSpiderVertex T)) : Prop :=
  S.Nonempty ∧ connectedWithin (doubleSpiderAdj T) S

def boundary (T : DoubleSpider)
    (S : Finset (DoubleSpiderVertex T)) : ℕ :=
  (Finset.univ.filter (fun e : DoubleSpiderVertex T × DoubleSpiderVertex T =>
    e.1 ∈ S ∧ e.2 ∉ S ∧ doubleSpiderAdj T e.1 e.2)).card

def connectedSubtreePolynomial (T : DoubleSpider) : SpiderPolynomial :=
  (Finset.univ.filter (connectedVertexSet T)).sum (fun S =>
    u ^ S.card * v ^ boundary T S)

def R (a : ℕ) : SpiderPolynomial :=
  u ^ a + v * Finset.sum (Finset.range a) (fun j => u ^ j)

def P (A : Multiset ℕ) : SpiderPolynomial :=
  (A.map R).prod

def I (a : ℕ) : SpiderPolynomial :=
  Finset.sum (Finset.Icc 1 a) (fun m =>
    (v + MvPolynomial.C (((a - m : ℕ) : ℤ)) * v ^ 2) * u ^ m)

def Ibridge (c : ℕ) : SpiderPolynomial :=
  Finset.sum (Finset.Icc 1 (c - 1)) (fun m =>
    MvPolynomial.C (((c - m : ℕ) : ℤ)) * u ^ m * v ^ 2)

def legCorrectionSum (A B : Multiset ℕ) : SpiderPolynomial :=
  Multiset.sum ((A + B).map I)

def exactBoundarySubtreeFactorization_claim19822 : Prop :=
  ∀ T : DoubleSpider, admissibleDoubleSpider T →
    connectedSubtreePolynomial T =
      u ^ (T.c + 1) * P T.A * P T.B +
        u * v * Finset.sum (Finset.range T.c) (fun j => u ^ j) *
          (P T.A + P T.B) +
        legCorrectionSum T.A T.B + Ibridge T.c

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19822
