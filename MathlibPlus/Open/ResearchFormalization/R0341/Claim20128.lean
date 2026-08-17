import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

open scoped BigOperators

abbrev PolynomialRing (F : Type*) [CommRing F] (k : ℕ) (E : Type*) :=
  MvPolynomial (Fin k × E) F

abbrev GenericField (F : Type*) [Field F] (k : ℕ) (E : Type*) :=
  FractionRing (PolynomialRing F k E)

noncomputable def columnRank {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (X : Finset E) : ℕ :=
  Matrix.rank (L.submatrix (fun r : R => r) (fun e : X => e.1))

noncomputable def finiteMatroidRatio {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (X : Finset E) : WithTop ℕ :=
  if h : columnRank L X = 0 then ⊤
  else ↑((X.card + columnRank L X - 1) / columnRank L X)

noncomputable def deckArboricity {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) : WithTop ℕ :=
  (Finset.univ.filter (fun X : Finset E => X.Nonempty)).sup
    (finiteMatroidRatio L)

noncomputable def genericDiagonalStack {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (k : ℕ) :
    Matrix (Fin (k + 1) × R) E (GenericField F k E) :=
  fun row e =>
    Fin.cases
      (algebraMap F (GenericField F k E) (L row.2 e))
      (fun i =>
        algebraMap F (GenericField F k E) (L row.2 e) *
          algebraMap (PolynomialRing F k E) (GenericField F k E)
            (MvPolynomial.X (i, e)))
      row.1

def genericStackInjective {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (k : ℕ) : Prop :=
  Function.Injective (Matrix.mulVecLin (genericDiagonalStack L k))

noncomputable def leastInjectiveStackSize {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) : WithTop ℕ :=
  sInf {q : WithTop ℕ |
    ∃ k : ℕ, q = ((k + 1 : ℕ) : WithTop ℕ) ∧ genericStackInjective L k}

def minimumGenericObservables_claim20128 : Prop :=
  ∀ (F R E : Type*) [Field F] [Infinite F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F),
    leastInjectiveStackSize L = deckArboricity L ∧
      (∀ k : ℕ,
        (genericStackInjective L k ↔
          deckArboricity L ≤ ((k + 1 : ℕ) : WithTop ℕ)))

end MathlibPlus.Open.ResearchFormalization.R0341.Claim20128
