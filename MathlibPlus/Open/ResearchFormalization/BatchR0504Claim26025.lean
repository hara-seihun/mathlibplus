import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26025

attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev Eight := Fin 8
private abbrev Index (N : ℕ) := Fin (N + 1)
private abbrev FoldIndex (N : ℕ) := Fin (N / 2 + 1)
private abbrev RawCoordinates (N : ℕ) :=
  (Index N → ℚ) × (Index N → ℚ) × (Index N → ℚ) ×
    (FoldIndex N → ℚ)
private abbrev ParameterCarrier :=
  (Fin 4 → ℚ) × (Fin 6 → ℚ) × (Fin 4 → ℚ) × ℚ

private def index (N t : ℕ) : Index N :=
  Fin.ofNat (N + 1) t

private def foldedIndex (N t : ℕ) : FoldIndex N :=
  Fin.ofNat (N / 2 + 1) (min t (N - t))

private def isComposition (N : ℕ) (μ : Eight → ℕ) : Prop :=
  (∑ i : Eight, μ i) = N

private def monomialRow (μ : Eight → ℕ) : MvPolynomial (Fin 2) ℚ :=
  ∏ i : Eight,
    (1 + MvPolynomial.X (0 : Fin 2) *
      (MvPolynomial.X (1 : Fin 2)) ^ μ i)

private def monomialRowSet (N : ℕ) : Set (MvPolynomial (Fin 2) ℚ) :=
  {p | ∃ μ : Eight → ℕ, isComposition N μ ∧ p = monomialRow μ}

private def monomialSpan (N : ℕ) :
    Submodule ℚ (MvPolynomial (Fin 2) ℚ) :=
  Submodule.span ℚ (monomialRowSet N)

private def monomialSpanDimension (N : ℕ) : ℕ :=
  Module.finrank ℚ (monomialSpan N)

private def singletonProfile (N : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  fun t => ∑ i : Eight, if μ i = t.1 then 1 else 0

private def pairProfile (N : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  fun t => ∑ i : Eight, ∑ j ∈ Finset.Ioi i,
    if μ i + μ j = t.1 then 1 else 0

private def tripleProfile (N : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  fun t => ∑ i : Eight, ∑ j ∈ Finset.Ioi i,
    ∑ r ∈ Finset.Ioi j,
      if μ i + μ j + μ r = t.1 then 1 else 0

private def fourProfile (N : ℕ) (μ : Eight → ℕ) : FoldIndex N → ℚ :=
  fun t =>
    ∑ S ∈ (Finset.univ : Finset Eight).powerset.filter
        (fun S => S.card = 4),
      if foldedIndex N (∑ i ∈ S, μ i) = t then 1 else 0

private def compressedRow (N : ℕ) (μ : Eight → ℕ) : RawCoordinates N :=
  (singletonProfile N μ, pairProfile N μ, tripleProfile N μ, fourProfile N μ)

private def compressedRowSet (N : ℕ) : Set (RawCoordinates N) :=
  {v | ∃ μ : Eight → ℕ, isComposition N μ ∧ v = compressedRow N μ}

private def compressedRowSpan (N : ℕ) :
    Submodule ℚ (RawCoordinates N) :=
  Submodule.span ℚ (compressedRowSet N)

private def coefficientPairing (N : ℕ) (c : RawCoordinates N)
    (μ : Eight → ℕ) : ℚ :=
  (∑ i : Eight, c.1 (index N (μ i))) +
    (∑ i : Eight, ∑ j ∈ Finset.Ioi i,
      c.2.1 (index N (μ i + μ j))) +
    (∑ i : Eight, ∑ j ∈ Finset.Ioi i,
      ∑ r ∈ Finset.Ioi j,
        c.2.2.1 (index N (μ i + μ j + μ r))) +
    (∑ S ∈ (Finset.univ : Finset Eight).powerset.filter
        (fun S => S.card = 4),
      c.2.2.2 (foldedIndex N (∑ i ∈ S, μ i)))

private def coordinatePairing (N : ℕ) (c v : RawCoordinates N) : ℚ :=
  (∑ t : Index N, c.1 t * v.1 t) +
    (∑ t : Index N, c.2.1 t * v.2.1 t) +
    (∑ t : Index N, c.2.2.1 t * v.2.2.1 t) +
    (∑ t : FoldIndex N, c.2.2.2 t * v.2.2.2 t)

private def reflectiveFour (N : ℕ) (l : FoldIndex N → ℚ) : Prop :=
  ∀ t : Index N,
    l (foldedIndex N t.1) = l (foldedIndex N (N - t.1))

private def annihilatorCondition (N : ℕ) (c : RawCoordinates N) : Prop :=
  reflectiveFour N c.2.2.2 ∧
    ∀ μ : Eight → ℕ, isComposition N μ →
      coefficientPairing N c μ = 0

private def annihilatorSet (N : ℕ) : Set (RawCoordinates N) :=
  {c | annihilatorCondition N c}

private def annihilatorSpace (N : ℕ) :
    Submodule ℚ (RawCoordinates N) :=
  Submodule.span ℚ (annihilatorSet N)

private def polynomialValue {n : ℕ} (a : Fin n → ℚ) (t : Index N) : ℚ :=
  ∑ i : Fin n, a i * (t.1 : ℚ) ^ i.1

private def sexticValue (N : ℕ) (d : Fin 4 → ℚ) (t : Index N) : ℚ :=
  d 0 +
    d 1 * ((t.1 : ℚ) * (N - t.1 : ℕ)) +
    d 2 * ((t.1 : ℚ) * (N - t.1 : ℕ)) ^ 2 +
    d 3 * ((t.1 : ℚ) * (N - t.1 : ℕ)) ^ 3

private def parameterL (N : ℕ) (p : ParameterCarrier) (t : Index N) : ℚ :=
  sexticValue N p.1 t

private def parameterK (N : ℕ) (p : ParameterCarrier) (t : Index N) : ℚ :=
  polynomialValue p.2.1 t - 2 * parameterL N p t

private def parameterH (N : ℕ) (p : ParameterCarrier) (t : Index N) : ℚ :=
  polynomialValue p.2.2.1 t - 3 * parameterK N p t -
    parameterK N p (index N (N - t.1)) - 6 * parameterL N p t

private def parameterA (N : ℕ) (p : ParameterCarrier) : ℚ :=
  (5 * parameterH N p (index N N) +
      15 * parameterH N p (index N 0) +
      24 * parameterK N p (index N N) +
      40 * parameterK N p (index N 0) +
      90 * parameterL N p (index N 0) -
      p.2.2.2 * (N : ℚ)) / 8

private def parameterF (N : ℕ) (p : ParameterCarrier) (t : Index N) : ℚ :=
  parameterA N p + p.2.2.2 * (t.1 : ℚ) -
    5 * parameterH N p t - parameterH N p (index N (N - t.1)) -
    10 * parameterK N p t - 5 * parameterK N p (index N (N - t.1)) -
    20 * parameterL N p t

private def parameterToRaw (N : ℕ) (p : ParameterCarrier) :
    RawCoordinates N :=
  (parameterF N p,
    parameterH N p,
    parameterK N p,
    fun t => parameterL N p (index N t.1))

private def exactParameterization (N : ℕ) : Prop :=
  (∀ c : RawCoordinates N, annihilatorCondition N c →
    ∃! p : ParameterCarrier, c = parameterToRaw N p) ∧
  (∀ p : ParameterCarrier, annihilatorCondition N (parameterToRaw N p))

private def ambientDimension (N : ℕ) : ℕ :=
  3 * N + N / 2 + 4

private def stableRank (N : ℕ) : ℕ :=
  3 * N + N / 2 - 11

/-- The exact coefficient carrier uses singleton, pair, triple, and one
folded four-subset block.  Its annihilator equations are the displayed
composition equations, and the parameter coordinates are explicitly tied to
l, p5, p3, and B. -/
def fifteenDimensionalAnnihilatorAndExactRank_claim26025 : Prop :=
  ∀ N : ℕ, 8 ≤ N →
    Module.finrank ℚ (RawCoordinates N) = ambientDimension N ∧
    Module.finrank ℚ ParameterCarrier = 15 ∧
    (∀ c : RawCoordinates N,
      c ∈ annihilatorSpace N ↔ annihilatorCondition N c) ∧
    Module.finrank ℚ (annihilatorSpace N) = 15 ∧
    exactParameterization N ∧
    (∀ (c : RawCoordinates N) (μ : Eight → ℕ),
      isComposition N μ →
        coefficientPairing N c μ = coordinatePairing N c (compressedRow N μ)) ∧
    Module.finrank ℚ (compressedRowSpan N) =
      Module.finrank ℚ (RawCoordinates N) -
        Module.finrank ℚ (annihilatorSpace N) ∧
    Module.finrank ℚ (compressedRowSpan N) = stableRank N ∧
    monomialSpanDimension N = Module.finrank ℚ (compressedRowSpan N) ∧
    monomialSpanDimension N = stableRank N

end MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26025
