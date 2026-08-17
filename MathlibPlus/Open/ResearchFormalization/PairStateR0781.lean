import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0781

noncomputable section

private def normalizedPairState
    {R : Type*} [CommRing R]
    (A B : Polynomial R) (t w : R) : Polynomial R :=
  Polynomial.C t + Polynomial.C w * (A + B) + A * B

private def blownUpPairState
    {R : Type*} [CommRing R]
    (A B : Polynomial R) (t w : R) : Polynomial R :=
  Polynomial.X ^ 3 * normalizedPairState A B t w

/-- Claim 24626: the coefficient exposed by the exact two-scale blow-up is
`t+w(a+b)+ab`, with a and b the constant evaluations of the symbolic child
polynomials. -/
def claim24626 : Prop :=
  ∀ {R : Type*} [CommRing R]
    (A B : Polynomial R) (t w : R),
    (blownUpPairState A B t w).coeff 3 =
      t + w * (Polynomial.eval 0 A + Polynomial.eval 0 B) +
        Polynomial.eval 0 A * Polynomial.eval 0 B

private def pairStateFactor
    {R : Type*} [CommRing R]
    (a b : R) : Polynomial (Polynomial R) :=
  (Polynomial.X : Polynomial (Polynomial R)) +
    Polynomial.C (((Polynomial.X : Polynomial R) + Polynomial.C a) *
      ((Polynomial.X : Polynomial R) + Polynomial.C b))

private def pairStateCharacteristic
    {R : Type*} [CommRing R] {d : ℕ}
    (a b : Fin d → R) : Polynomial (Polynomial R) :=
  ∏ j : Fin d, pairStateFactor (a j) (b j)

private def childMarginalPolynomial
    {R : Type*} [CommRing R] {d : ℕ}
    (a b : Fin d → R) : Polynomial R :=
  ∏ j : Fin d,
    ((Polynomial.X : Polynomial R) + Polynomial.C (a j)) *
      ((Polynomial.X : Polynomial R) + Polynomial.C (b j))

/-- Claim 24629: a polynomial complete pair-state relation, rather than a
pointwise identity, specializes at T=0 to the child-cavity characteristic
relation. -/
def claim24629 : Prop :=
  ∀ {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin 3 → R) (a b : Fin 3 → Fin d → R),
    (∑ i : Fin 3,
      Polynomial.C (Polynomial.C (c i)) *
        pairStateCharacteristic (a i) (b i)) = 0 →
    (∑ i : Fin 3,
      Polynomial.C (c i) * childMarginalPolynomial (a i) (b i)) = 0

private abbrev Occurrence (d : ℕ) := Fin d ⊕ Fin d

private def occurrenceValue
    {R : Type*} {d : ℕ}
    (left right : Fin d → R) : Occurrence d → R
  | Sum.inl j => left j
  | Sum.inr j => right j

private def occurrenceMultiset
    {R : Type*} {d : ℕ}
    (left right : Fin d → R) : Multiset R :=
  (Finset.univ : Finset (Occurrence d)).val.map
    (occurrenceValue left right)

private def sameOccurrenceMultiset
    {R : Type*} {d : ℕ}
    (left right : Fin 3 → Fin d → R) : Prop :=
  ∀ i : Fin 3,
    occurrenceMultiset (left i) (right i) =
      occurrenceMultiset (left 0) (right 0)

private def isOccurrencePairing
    {d : ℕ}
    (M : Finset (Occurrence d × Occurrence d)) : Prop :=
  (∀ e ∈ M, e.1 ≠ e.2) ∧
    (∀ e ∈ M, (e.2, e.1) ∉ M) ∧
    (∀ p : Occurrence d,
      ∃! q : Occurrence d, (p, q) ∈ M ∨ (q, p) ∈ M)

private def pairingCharacteristic
    {R : Type*} [CommRing R] {d : ℕ}
    (left right : Fin d → R)
    (M : Finset (Occurrence d × Occurrence d)) :
    Polynomial (Polynomial R) :=
  ∏ e ∈ M, pairStateFactor
    (occurrenceValue left right e.1)
    (occurrenceValue left right e.2)

private def isPartnerOccurrence
    {R : Type*} {d : ℕ}
    (left right : Fin d → R)
    (M : Finset (Occurrence d × Occurrence d))
    (a b : R) : Prop :=
  ∃ p q : Occurrence d,
    occurrenceValue left right p = a ∧
      ((p, q) ∈ M ∨ (q, p) ∈ M) ∧
      occurrenceValue left right q = b

private def localPairFactor
    {K : Type*} [Field K]
    (a b : K) : Polynomial (Polynomial K) :=
  let ε : Polynomial (Polynomial K) := Polynomial.X
  let s : Polynomial K := Polynomial.X
  let w : Polynomial (Polynomial K) :=
    ε - Polynomial.C (Polynomial.C a)
  let T : Polynomial (Polynomial K) := ε * Polynomial.C s
  T + (w + Polynomial.C (Polynomial.C a)) *
    (w + Polynomial.C (Polynomial.C b))

private def normalizedLocalInitialForm
    {K : Type*} [Field K]
    (a b : K) : Polynomial K :=
  (b - a)⁻¹ • (localPairFactor a b).coeff 1

/-- Claim 24633: squarefree occurrence data provide only the nonzero partner
 difference; the normalized epsilon-initial local form is
`1+s/(b_i(a)-a)`. -/
def claim24633 : Prop :=
  ∀ {K : Type*} [Field K] {d : ℕ}
    (left right : Fin 3 → Fin d → K)
    (M : Fin 3 → Finset (Occurrence d × Occurrence d))
    (a : K) (partner : Fin 3 → K),
    sameOccurrenceMultiset (left := left) (right := right) ∧
      (occurrenceMultiset (left 0) (right 0)).Nodup ∧
      (∀ i : Fin 3, isOccurrencePairing (M i)) ∧
      (∀ i : Fin 3,
        isPartnerOccurrence (left i) (right i) (M i) a (partner i)) →
    ∀ i : Fin 3,
      normalizedLocalInitialForm a (partner i) =
        1 + (partner i - a)⁻¹ • (Polynomial.X : Polynomial K)

end
end MathlibPlus.Open.ResearchFormalization.R0781
