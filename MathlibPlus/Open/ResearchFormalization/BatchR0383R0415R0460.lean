import Mathlib

open scoped BigOperators Matrix
open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460

noncomputable section

/-- The reciprocal coefficient presentation used by the fixed transform claim. -/
def reciprocalCoefficientForm (g : ℕ) (a : Fin (g + 1) → ℤ) : Polynomial ℤ :=
  (∑ j : Fin g,
      C (a ⟨j.1, Nat.lt_succ_of_lt j.2⟩) *
        (X ^ j.1 + X ^ (2 * g - j.1))) +
    C (a ⟨g, Nat.lt_succ_self g⟩) * X ^ g

/-- The coefficient transform in Claim 20676. -/
def fixedCoefficientTransform (g : ℕ) (a : Fin (g + 1) → ℤ) : Polynomial ℤ :=
  (∑ j : Fin g, (
      C (a ⟨j.1, Nat.lt_succ_of_lt j.2⟩ * ((-1 : ℤ) ^ (g + j.1))) *
        X ^ j.1 +
      C (a ⟨j.1, Nat.lt_succ_of_lt j.2⟩) * X ^ (2 * g - j.1))) +
    C (a ⟨g, Nat.lt_succ_self g⟩) * X ^ g

/-- Reciprocality and skew-reciprocity are stated coefficientwise at degree `2*g`. -/
def IsReciprocalDegree (g : ℕ) (p : Polynomial ℤ) : Prop :=
  p.natDegree = 2 * g ∧
    ∀ j : ℕ, j ≤ 2 * g → p.coeff j = p.coeff (2 * g - j)

def IsSkewReciprocalDegree (g : ℕ) (p : Polynomial ℤ) : Prop :=
  p.natDegree = 2 * g ∧
    ∀ j : ℕ, j ≤ 2 * g →
      p.coeff j = ((-1 : ℤ) ^ (g + j)) * p.coeff (2 * g - j)

/-- Claim 20676. -/
def claim20676 : Prop :=
  ∀ (g : ℕ) (P : Polynomial ℤ) (a : Fin (g + 1) → ℤ),
    IsReciprocalDegree g P →
    P = reciprocalCoefficientForm g a →
    IsSkewReciprocalDegree g (fixedCoefficientTransform g a)

/-- A product of cyclotomic polynomials, with repeated factors represented by a multiset. -/
def IsCyclotomicPadding (p : Polynomial ℤ) : Prop :=
  ∃ s : Multiset ℕ,
    (∀ n : ℕ, n ∈ s → 0 < n) ∧
      (s.map Nat.totient).sum = 6 ∧
        p = (s.map (fun n => Polynomial.cyclotomic n ℤ)).prod ∧
          p.Monic ∧ p.natDegree = 6 ∧ p.constantCoeff = 1

def cyclotomicPaddingSet : Set (Polynomial ℤ) :=
  {p | IsCyclotomicPadding p}

/-- Claim 20669. -/
def claim20669 : Prop :=
  (∀ n : ℕ, (Nat.totient n : ℝ) ≥ Real.sqrt ((n : ℝ) / 2)) ∧
    (∀ n : ℕ, Nat.totient n ≤ 6 → n ≤ 72) ∧
      (∀ n : ℕ, 0 < n →
        (Nat.totient n ≤ 6 ↔
          n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
            n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 18))

/-- Claim 20670. -/
def claim20670 : Prop :=
  Set.Finite cyclotomicPaddingSet ∧ cyclotomicPaddingSet.ncard = 59

/-- The join of two finite families of finite sets. -/
def joinFamily {α : Type} [DecidableEq α]
    (A B : Finset (Finset α)) : Finset (Finset α) :=
  (A.product B).image (fun ab => ab.1 ∪ ab.2)

def IsUnionClosedFamily {α : Type} [DecidableEq α]
    (A : Finset (Finset α)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∪ b ∈ A

def HasEmptyTotalIntersection {α : Type} [DecidableEq α]
    (A : Finset (Finset α)) : Prop :=
  ∀ x : α, ∃ a ∈ A, x ∉ a

/-- Claim 21142. -/
def claim21142 : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    A.Nonempty → B.Nonempty →
    (∅ : Finset α) ∉ A → (∅ : Finset α) ∉ B →
    IsUnionClosedFamily A → IsUnionClosedFamily B →
    HasEmptyTotalIntersection A → HasEmptyTotalIntersection B →
    (joinFamily A B).card = 6 → min A.card B.card ≤ 12

/-- A labelled wedge in the complete graph on `Fin n`. -/
def IsLabelledWedge {n : ℕ}
    (t : Finset (Finset (Fin n))) : Prop :=
  ∃ x u v : Fin n,
    x ≠ u ∧ x ≠ v ∧ u ≠ v ∧ t = {{x, u}, {x, v}}

def completeEdges (n : ℕ) : Set (Finset (Fin n)) :=
  {e | e.card = 2}

def labelledWedges (n : ℕ) : Set (Finset (Finset (Fin n))) :=
  {t | IsLabelledWedge t}

def IsMatching {n : ℕ}
    (C : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ C, ∀ f ∈ C, e ≠ f → e ∩ f = ∅

def wedgeContainingEdgeSet (n : ℕ) : Set (Finset (Finset (Fin n))) :=
  {C | (C : Set (Finset (Fin n))) ⊆ completeEdges n ∧
    ∃ t ∈ labelledWedges n, t ⊆ C}

def wedgeCoordinate (n : ℕ)
    (t : Finset (Finset (Fin n))) : Set (Finset (Finset (Fin n))) :=
  {C | C ∈ wedgeContainingEdgeSet n ∧ t ⊆ C}

/-- Claim 21682. -/
def claim21682 : Prop :=
  ∀ n : ℕ,
    wedgeContainingEdgeSet n =
      {C : Finset (Finset (Fin n)) |
      (C : Set (Finset (Fin n))) ⊆ completeEdges n ∧ ¬ IsMatching C} ∧
      ∀ C ∈ wedgeContainingEdgeSet n,
        ∃ t ∈ labelledWedges n, C ∈ wedgeCoordinate n t

/-- Matrices on the two halves of a rank `2*g` integral lattice. -/
abbrev SplitIndex (g : ℕ) := Fin g ⊕ Fin g

def standardSymplectic (g : ℕ) : Matrix (SplitIndex g) (SplitIndex g) ℤ :=
  Matrix.fromBlocks 0 1 (-1) 0

def omegaFromA (g : ℕ) (A : Matrix (Fin g) (Fin g) ℤ) :
    Matrix (SplitIndex g) (SplitIndex g) ℤ :=
  Matrix.fromBlocks 0 A (-A.transpose) 0

def isMatrixInvolution {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℤ) : Prop :=
  J * J = 1

def isSymmetricMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℤ) : Prop :=
  B.transpose = B

def isUnimodularMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℤ) : Prop :=
  IsUnit B.det

def isAntiSymplecticMatrix (g : ℕ)
    (J : Matrix (SplitIndex g) (SplitIndex g) ℤ) : Prop :=
  J.transpose * standardSymplectic g * J = -(standardSymplectic g)

def isAntiSymplecticWith (Ω J : Matrix (SplitIndex g) (SplitIndex g) ℤ) : Prop :=
  J.transpose * Ω * J = -Ω

def isSymplecticWith (Ω S : Matrix (SplitIndex g) (SplitIndex g) ℤ) : Prop :=
  S.transpose * Ω * S = Ω

def isCongruentIdentityModTwo {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℤ) : Prop :=
  ∀ i j, ∃ k : ℤ, J i j - (1 : Matrix ι ι ℤ) i j = 2 * k

def eigenspacePlus {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℤ) : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (Matrix.toLin' J - LinearMap.id)

def eigenspaceMinus {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℤ) : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (Matrix.toLin' J + LinearMap.id)

def involutionIndex {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℤ) : ℕ :=
  Nat.card ((ι → ℤ) ⧸ (eigenspacePlus J ⊔ eigenspaceMinus J))

def isSplitInvolution {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℤ) : Prop :=
  involutionIndex J = 1

def isMaximallyNonsplit (g : ℕ)
    (J : Matrix (SplitIndex g) (SplitIndex g) ℤ) : Prop :=
  involutionIndex J = 2 ^ g

/-- Claim 20681. -/
def claim20681 : Prop :=
  (∀ (g : ℕ) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ),
    isMatrixInvolution J →
      ∃ r : ℕ, r ≤ g ∧ involutionIndex J = 2 ^ r ∧
        (isSplitInvolution J → r = 0) ∧
        (involutionIndex J = 2 ^ g → r = g)) ∧
    (∃ (g : ℕ) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (r : ℕ),
      0 < r ∧ r < g ∧ isMatrixInvolution J ∧ involutionIndex J = 2 ^ r)

/-- The block involution attached to an integral inverse of `B`. -/
def blockInvolution {g : ℕ}
    (B Binv : Matrix (Fin g) (Fin g) ℤ) :
    Matrix (SplitIndex g) (SplitIndex g) ℤ :=
  Matrix.fromBlocks 0 B Binv 0

/-- Claim 20682. -/
def claim20682 : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ),
    isSymmetricMatrix B → isUnimodularMatrix B →
      ∃ Binv : Matrix (Fin g) (Fin g) ℤ,
        B * Binv = 1 ∧ Binv * B = 1 ∧
          let J := blockInvolution B Binv
          isMatrixInvolution J ∧ isAntiSymplecticMatrix g J ∧ isMaximallyNonsplit g J

/-- Integral upper-unitriangular matrices have an integral inverse. -/
def isUpperUnitriangular {g : ℕ}
    (A : Matrix (Fin g) (Fin g) ℤ) : Prop :=
  (∀ i : Fin g, A i i = 1) ∧
    (∀ i j : Fin g, i > j → A i j = 0)

/-- Claim 20680. -/
def claim20680 : Prop :=
  ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) ℤ),
    isUpperUnitriangular A →
      ∃ Ainv : Matrix (Fin g) (Fin g) ℤ,
        A * Ainv = 1 ∧ Ainv * A = 1 ∧
          let D := Matrix.fromBlocks (1 : Matrix (Fin g) (Fin g) ℤ) 0 0 Ainv
          D.transpose * omegaFromA g A * D = standardSymplectic g

def isReciprocalSumDegree (g : ℕ) (p : Polynomial ℤ) : Prop :=
  p.natDegree = g + g ∧
    ∀ j : ℕ, j ≤ g + g → p.coeff j = p.coeff (g + g - j)

def inverseSeriesCoefficients (P : Polynomial ℤ) (b : ℕ → ℤ) : Prop :=
  ∀ n : ℕ,
    (∑ k ∈ Finset.range (n + 1), P.coeff k * b (n - k)) =
      if n = 0 then 1 else 0

def toeplitzAtZero (g : ℕ) (b : ℕ → ℤ) : Matrix (Fin g) (Fin g) ℤ :=
  fun i j => if i ≤ j then b (j.1 - i.1) else 0

/-- The multiplication-by-`x` companion in the basis `1,x,...,x^(n-1)`. -/
def ordinaryCompanion (P : Polynomial ℤ) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if j.1 + 1 < n ∧ i.1 = j.1 + 1 then 1
    else if j.1 + 1 = n then -P.coeff i.1
    else 0

def splitCompanion (g : ℕ) (P : Polynomial ℤ) :
    Matrix (SplitIndex g) (SplitIndex g) ℤ :=
  Matrix.reindex
    (finSumFinEquiv (m := g) (n := g)).symm
    (finSumFinEquiv (m := g) (n := g)).symm
    (ordinaryCompanion P (g + g))

def halfSignInvolution (g : ℕ) : Matrix (SplitIndex g) (SplitIndex g) ℤ :=
  Matrix.fromBlocks (-(1 : Matrix (Fin g) (Fin g) ℤ)) 0 0 1

/-- Claim 20678. -/
def claim20678 : Prop :=
  ∀ (g : ℕ) (P : Polynomial ℤ) (b : ℕ → ℤ),
    P.Monic → P.natDegree = g + g → P.constantCoeff = 1 →
    isReciprocalSumDegree g P → inverseSeriesCoefficients P b →
      let A := toeplitzAtZero g b
      let Ω := omegaFromA g A
      let C := splitCompanion g P
      isUpperUnitriangular A ∧ IsUnit Ω.det ∧ C.transpose * Ω * C = Ω

/-- Claim 20679. -/
def claim20679 : Prop :=
  ∀ (g : ℕ) (P : Polynomial ℤ) (b : ℕ → ℤ),
    P.Monic → P.natDegree = g + g → P.constantCoeff = 1 →
    isReciprocalSumDegree g P → inverseSeriesCoefficients P b →
      let A := toeplitzAtZero g b
      let Ω := omegaFromA g A
      let C := splitCompanion g P
      let R := halfSignInvolution g
      R.transpose * Ω * R = -Ω ∧
        Matrix.charpoly (R * C) =
          fixedCoefficientTransform g (fun j => P.coeff j.1)

def complexPolynomial (p : Polynomial ℤ) : Polynomial ℂ :=
  p.map (Int.castRingHom ℂ)

def integerMahlerMeasure (p : Polynomial ℤ) : ℝ :=
  |(p.leadingCoeff : ℝ)| *
    ((complexPolynomial p).roots.map (fun z => max 1 ‖z‖)).prod

def traceLift (q : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (m + 1),
    ∑ j ∈ Finset.range (k + 1),
      C (q.coeff k * (Nat.choose k j : ℤ)) *
        X ^ (m + k - 2 * j)

def traceRootGeometry (q : Polynomial ℤ) (T : ℝ) : Prop :=
  T > 2 ∧
    Polynomial.eval (Complex.ofReal T) (complexPolynomial q) = 0 ∧
      (∀ z : ℂ, z ∈ (complexPolynomial q).roots →
        ((2 < z.re ∧ z.im = 0) ↔ z = Complex.ofReal T)) ∧
        (∀ z : ℂ, z ∈ (complexPolynomial q).roots → z ≠ Complex.ofReal T →
          z.im = 0 ∧ -2 < z.re ∧ z.re < 2)

def liftedRoot (T : ℝ) : ℝ :=
  (T + Real.sqrt (T ^ 2 - 4)) / 2

def isTracePairRoot (T : ℝ) (z : ℂ) : Prop :=
  z + z⁻¹ = Complex.ofReal T

/-- Claim 20698. -/
def claim20698 : Prop :=
  ∀ (m : ℕ) (q : Polynomial ℤ) (T : ℝ),
    q.Monic → q.natDegree = m → traceRootGeometry q T →
      let Q := traceLift q m
      Q.Monic ∧ Q.natDegree = 2 * m ∧ IsReciprocalDegree m Q ∧
        (∀ z : ℂ, z ≠ 0 →
          Polynomial.eval z (complexPolynomial Q) =
            z ^ m * Polynomial.eval (z + z⁻¹) (complexPolynomial q)) ∧
        (∀ z : ℂ, z ∈ (complexPolynomial Q).roots →
          ¬ isTracePairRoot T z → ‖z‖ = 1) ∧
        integerMahlerMeasure Q = liftedRoot T

/-- Claim 20684. -/
def claim20684 : Prop :=
  ∀ (g : ℕ) (P : Polynomial ℤ) (b : ℕ → ℤ)
      (J : Matrix (SplitIndex g) (SplitIndex g) ℤ),
    P.Monic → P.natDegree = g + g → P.constantCoeff = 1 →
    isReciprocalSumDegree g P → inverseSeriesCoefficients P b →
    isMatrixInvolution J →
    let A := toeplitzAtZero g b
    let Ω := omegaFromA g A
    let C := splitCompanion g P
    isAntiSymplecticWith Ω J → isSplitInvolution J →
      (∃ S Sinv : Matrix (SplitIndex g) (SplitIndex g) ℤ,
        S * Sinv = 1 ∧ Sinv * S = 1 ∧ isSymplecticWith Ω S ∧
          Sinv * J * S = halfSignInvolution g) ∧
      isCongruentIdentityModTwo J ∧
        Polynomial.map (Int.castRingHom (ZMod 2)) (Matrix.charpoly (J * C)) =
          Polynomial.map (Int.castRingHom (ZMod 2)) P

end

end MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460
