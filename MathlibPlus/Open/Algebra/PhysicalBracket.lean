import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.PhysicalBracket

noncomputable section

/-- Increasing unordered pairs of complete physical types. -/
abbrev TypePair (ι : Type*) [LinearOrder ι] :=
  {p : ι × ι // p.1 < p.2}

instance typePairDecidableEq {ι : Type*} [LinearOrder ι] [DecidableEq ι] :
    DecidableEq (TypePair ι) := Classical.decEq _

/-- The specialized bracket `p_{αβ}=t_β-t_α`. -/
def physicalBracket {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (p : TypePair ι) : MvPolynomial ι ℚ :=
  MvPolynomial.X p.1.2 - MvPolynomial.X p.1.1

/-- The two-column evaluation matrix for one physical bracket. -/
def physicalColumnMatrix {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (p : TypePair ι) : Matrix (Fin 2) (Fin 2) (MvPolynomial ι ℚ) :=
  fun i j =>
    if i.1 = 0 then 1
    else if j.1 = 0 then MvPolynomial.X p.1.1
    else MvPolynomial.X p.1.2

/-- A monomial in the irreducible type-pair bracket factors. -/
def bracketMonomial {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (e : TypePair ι →₀ ℕ) : MvPolynomial ι ℚ :=
  Finset.prod e.support (fun p => physicalBracket p ^ e p)

/-- Claim 45488: no nonzero binomial relation survives physical bracket
specialization. -/
def physicalPluckerBinomialFaithful_45488 : Prop :=
  ∀ {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (p : TypePair ι),
    Matrix.det (physicalColumnMatrix p) = physicalBracket p ∧
    ∀ (e f : TypePair ι →₀ ℕ) (c d : ℚ),
      c ≠ 0 → d ≠ 0 →
      MvPolynomial.C c * bracketMonomial e =
        MvPolynomial.C d * bracketMonomial f →
      e = f ∧ c = d

/-- The canonical unordered physical type pair, or `none` for equal types. -/
def canonicalTypePair {ι : Type*} [LinearOrder ι]
    (a b : ι) : Option (TypePair ι) :=
  if h : a < b then some ⟨(a, b), h⟩
  else if h : b < a then some ⟨(b, a), h⟩
  else none

/-- Exponent aggregation after identifying occurrence columns by complete type. -/
def aggregateOccurrenceExponent {ι κ : Type*}
    [LinearOrder ι] [LinearOrder κ] [DecidableEq ι] [DecidableEq κ]
    (occ : κ → ι) (e : TypePair κ →₀ ℕ) (q : TypePair ι) : ℕ :=
  Finset.sum e.support (fun p =>
    if canonicalTypePair (occ p.1.1) (occ p.1.2) = some q then e p else 0)

/-- Evaluation of an occurrence monomial after physical-type identification. -/
def occurrenceMonomial {ι κ : Type*}
    [LinearOrder ι] [LinearOrder κ] [DecidableEq ι] [DecidableEq κ]
    (occ : κ → ι) (e : TypePair κ →₀ ℕ) : MvPolynomial ι ℚ :=
  Finset.prod e.support (fun p =>
    match canonicalTypePair (occ p.1.1) (occ p.1.2) with
    | none => 0
    | some q => physicalBracket q ^ e p)

/-- Claim 45489: after discarding zero equal-type brackets, occurrence
identification creates no new nonzero two-term relation. -/
def repeatedTypeNoNewBinomial_45489 : Prop :=
  ∀ {ι κ : Type*}
    [LinearOrder ι] [LinearOrder κ] [DecidableEq ι] [DecidableEq κ]
    (occ : κ → ι)
    (e f : TypePair κ →₀ ℕ) (c d : ℚ),
    c ≠ 0 → d ≠ 0 →
    occurrenceMonomial occ e ≠ 0 → occurrenceMonomial occ f ≠ 0 →
    MvPolynomial.C c * occurrenceMonomial occ e =
      MvPolynomial.C d * occurrenceMonomial occ f →
    c = d ∧
      ∀ q : TypePair ι,
        aggregateOccurrenceExponent occ e q =
          aggregateOccurrenceExponent occ f q

/-- A monomial with independent type-bracket, spectator, and connector
variable sectors. -/
def contextMonomial {ι σ κ : Type*}
    [LinearOrder ι] [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
    (e : TypePair ι →₀ ℕ) (s : σ →₀ ℕ) (c : κ →₀ ℕ) :
    MvPolynomial (ι ⊕ (σ ⊕ κ)) ℚ :=
  (Finset.prod e.support (fun p =>
      (MvPolynomial.X (Sum.inl p.1.2) -
        MvPolynomial.X (Sum.inl p.1.1)) ^ e p)) *
    (Finset.prod s.support (fun x =>
      MvPolynomial.X (Sum.inr (Sum.inl x)) ^ s x)) *
    (Finset.prod c.support (fun x =>
      MvPolynomial.X (Sum.inr (Sum.inr x)) ^ c x))

/-- Claim 45490: independent complete context sectors preserve UFD
faithfulness. -/
def contextFactorFaithfulness_45490 : Prop :=
  ∀ {ι σ κ : Type*}
    [LinearOrder ι] [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
    (e f : TypePair ι →₀ ℕ)
    (s t : σ →₀ ℕ) (c d : κ →₀ ℕ) (a b : ℚ),
    a ≠ 0 → b ≠ 0 →
    MvPolynomial.C a * contextMonomial e s c =
      MvPolynomial.C b * contextMonomial f t d →
    a = b ∧ e = f ∧ s = t ∧ c = d

end
end MathlibPlus.Open.Algebra.PhysicalBracket
