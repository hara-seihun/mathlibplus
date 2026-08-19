import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0504Claim26012

attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev Eight := Fin 8
private abbrev Index (N : ℕ) := Fin (N + 1)
private abbrev FoldIndex (N : ℕ) := Fin (N / 2 + 1)
private abbrev RawCoordinates (N : ℕ) :=
  (Index N → ℚ) × (Index N → ℚ) × (Index N → ℚ) ×
    (FoldIndex N → ℚ)

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

private def subsetProfile (N r : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  fun t =>
    ∑ S ∈ (Finset.univ : Finset Eight).powerset.filter
        (fun S => S.card = r),
      if (∑ i ∈ S, μ i) = t.1 then 1 else 0

private def singletonProfile (N : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  subsetProfile N 1 μ

private def pairProfile (N : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  subsetProfile N 2 μ

private def tripleProfile (N : ℕ) (μ : Eight → ℕ) : Index N → ℚ :=
  subsetProfile N 3 μ

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

private def blockReciprocity (N : ℕ) (μ : Eight → ℕ) : Prop :=
  (∀ t : Index N,
    subsetProfile N 5 μ t =
      subsetProfile N 3 μ (index N (N - t.1))) ∧
  (∀ t : Index N,
    subsetProfile N 6 μ t =
      subsetProfile N 2 μ (index N (N - t.1))) ∧
  (∀ t : Index N,
    subsetProfile N 7 μ t =
      subsetProfile N 1 μ (index N (N - t.1))) ∧
  (∀ t : Index N,
    subsetProfile N 4 μ t =
      subsetProfile N 4 μ (index N (N - t.1)))

/-- Reciprocity identifies the complementary subset blocks on the exact
nonnegative eight-composition carrier.  The product span and the span of the
singleton, pair, triple, and folded four-subset blocks have the same dimension;
for `N ≥ 8`, the latter's free ambient dimension is
`3N + floor(N/2) + 4`. -/
def reciprocityCompressionToFourFreeBlocks_claim26012 : Prop :=
  (∀ N : ℕ, ∀ μ : Eight → ℕ,
    isComposition N μ → blockReciprocity N μ) ∧
  (∀ N : ℕ,
    monomialSpanDimension N = Module.finrank ℚ (compressedRowSpan N)) ∧
  (∀ N : ℕ, 8 ≤ N →
    Module.finrank ℚ (RawCoordinates N) = 3 * N + N / 2 + 4)

end MathlibPlus.Open.ResearchFormalization.R0504Claim26012
