import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators
open MvPolynomial
open Classical

namespace MathlibPlus.Open.Algebra.NewResearch2.C0112Repair

noncomputable section

/-- Complete-homogeneous evaluation on the consecutive flag values. -/
def completeHomogeneousEval {R : Type*} [CommSemiring R]
    (r q : ℕ) (a : R) : R :=
  eval₂ (RingHom.id R) (fun i : Fin (r + 2) => a + (i.1 : R))
    (hsymm (Fin (r + 2)) R q)

/-- The flagged array, including the zero convention for a negative degree. -/
def flaggedArray {R : Type*} [CommSemiring R] (a : R) (r j : ℕ) : R :=
  (r + 1 : R) *
    if r + 1 ≤ 2 * j then
      completeHomogeneousEval r (2 * j - r - 1) a
    else 0

/-- The row set attached to a padded partition, in zero-based `Fin` notation. -/
def partitionRowSet (d : ℕ) (part : Fin d → ℕ) : Fin d → ℕ :=
  fun i => i.1 + part (Fin.rev i)

/-- The flagged minor indexed by a row set. -/
def flaggedMinor {R : Type*} [CommRing R]
    (a : R) (d : ℕ) (K : Fin d → ℕ) : R :=
  Matrix.det (fun (i : Fin d) (j : Fin d) =>
    flaggedArray a (K i) (j.1 + 1))

/-- Claim 1735: the padded-partition row set and its flagged determinant. -/
def partitionRowSetAndFlaggedMinor_claim1735_repair : Prop :=
  ∀ (R : Type*) [CommRing R] (a : R) (d : ℕ)
    (part : Fin d → ℕ),
    Antitone part →
      flaggedMinor a d (partitionRowSet d part) =
        Matrix.det (fun (i : Fin d) (j : Fin d) =>
          flaggedArray a (partitionRowSet d part i) (j.1 + 1))

/-- The two-row partition padded to `d` entries. -/
def twoRowPartition (d n k : ℕ) : Fin d → ℕ :=
  fun i => if i.1 = 0 then n else if i.1 = 1 then k else 0

/-- The row set of the two-row partition, using the same reversal as `K_λ`. -/
def twoRowRowSet (d n k : ℕ) : Fin d → ℕ :=
  partitionRowSet d (twoRowPartition d n k)

/-- The explicit row-set list used to display the selected/unselected word. -/
def twoRowRowSetList (d n k : ℕ) : List ℕ :=
  List.range (d - 2) ++ [d + k - 2, d + n - 1]

/-- `S` is true and `U` is false in the selected/unselected word. -/
def twoRowSelectedUnselectedWord (d n k : ℕ) : List Bool :=
  (List.range (2 * d + 2)).map (fun p =>
    if p = 0 ∨ p - 1 ∈ twoRowRowSetList d n k then true else false)

/-- Claim 1741: the selected/unselected word for a padded two-row partition. -/
def twoRowSelectedUnselectedWord_claim1741_repair : Prop :=
  ∀ (d n k : ℕ), k ≤ n → max n (k + 1) ≤ d →
    twoRowSelectedUnselectedWord d n k =
      List.replicate (d - 1) true ++ List.replicate k false ++ [true] ++
        List.replicate (n - k) false ++ [true] ++
        List.replicate (d - n + 1) false

/-- The half-shift variable in the polynomial ring `ℚ[b]`. -/
def bVariable : Polynomial ℚ := Polynomial.X

/-- The flagged-array parameter `a=b+1/2`. -/
def aVariable : Polynomial ℚ :=
  bVariable + Polynomial.C (1 / 2 : ℚ)

/-- The principal row set and principal minor. -/
def principalRow (d : ℕ) : Fin d → ℕ := fun i => i.1

def principalMinor (d : ℕ) : Polynomial ℚ :=
  flaggedMinor aVariable d (principalRow d)

/-- The rising product `(Y)_m`. -/
def halfShiftY (d : ℕ) : Polynomial ℚ :=
  2 * bVariable + Polynomial.C ((d + 1 : ℕ) : ℚ)

def risingProduct (Y : Polynomial ℚ) (m : ℕ) : Polynomial ℚ :=
  Finset.prod (Finset.range m) (fun r => Y + Polynomial.C (r : ℚ))

/-- `Δ_(n,k)=(Y-1)(Y)_(k-1)(Y)_n`, with the literal `Y-1` factor. -/
def correctionDenominator (d n k : ℕ) : Polynomial ℚ :=
  (halfShiftY d - Polynomial.C 1) *
    risingProduct (halfShiftY d) (k - 1) *
    risingProduct (halfShiftY d) n

/-- The neighboring-minor polynomial `H_(n,k)`. -/
def twoRowMinor (d n k : ℕ) : Polynomial ℚ :=
  flaggedMinor aVariable d (twoRowRowSet d n k)

/-- `S_(n,k)=∑_{j=0}^k(-1)^j H_(n,j)`. -/
def alternatingMinorSum (d n k : ℕ) : Polynomial ℚ :=
  Finset.sum (Finset.range (k + 1)) (fun j =>
    (-1 : Polynomial ℚ) ^ j * twoRowMinor d n j)

/-- The `k≥1` neighboring-minor numerator and its `k=0` base. -/
def correctionNumeratorPositiveIndex (d n k : ℕ) : Polynomial ℚ :=
  Polynomial.C
      (((((d : ℤ) + (k : ℤ) - 1 : ℤ) : ℚ) *
        ((d + n : ℕ) : ℚ)) /
        (((d - 1 : ℕ) : ℚ) * (d : ℚ))) *
    (Polynomial.C (Nat.choose (d - 1) k : ℚ) *
        Polynomial.C (Nat.choose d n : ℚ) -
      Polynomial.C (Nat.choose (d - 1) (n + 1) : ℚ) *
        Polynomial.C (Nat.choose d (k - 1) : ℚ))

def correctionNumeratorBase (d n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((((d + n : ℕ) : ℚ) / (d : ℚ)) *
    (Nat.choose d n : ℚ))

/-- `Z_(n,k)`, with the separately stated `k=0` normalization. -/
def correctionNumerator (d n k : ℕ) : Polynomial ℚ :=
  if k = 0 then correctionNumeratorBase d n
  else correctionNumeratorPositiveIndex d n k

/-- The correction family, including its `k=0` base. -/
def correctionPolynomial (d n k : ℕ) : Polynomial ℚ :=
  if k = 0 then correctionNumeratorBase d n
  else correctionDenominator d n k * alternatingMinorSum d n k /
    principalMinor d

/-- Claim 1749: the cleared alternating-minor correction and its exact recurrence. -/
def correctionRecurrence_claim1749_repair : Prop :=
  ∀ (d n k : ℕ), 1 ≤ k → k ≤ n → max n (k + 1) ≤ d →
    correctionPolynomial d n 0 = correctionNumerator d n 0 ∧
      correctionPolynomial d n k =
        (halfShiftY d + Polynomial.C (((((k : ℤ) - 2 : ℤ) : ℚ))) ) *
            correctionPolynomial d n (k - 1) +
          (-1 : Polynomial ℚ) ^ k * correctionNumerator d n k

/-- A Catalan-admissible row set, with the source's one-based bound. -/
def catalanRowSet (d : ℕ) (K : Fin d → ℕ) : Prop :=
  StrictMono K ∧ ∀ i : Fin d, K i ≤ 2 * i.1 + 1

/-- The finite row-set carrier obtained from all functions into the endpoint range. -/
def rowCandidates (d : ℕ) : Finset (Fin d → ℕ) :=
  (Finset.univ : Finset (Fin d → Fin (2 * d + 2))).image
    (fun K i => (K i).1)

/-- The Catalan-admissible rows used by the cup frame. -/
def admissibleRows (d : ℕ) : Finset (Fin d → ℕ) :=
  @Finset.filter (Fin d → ℕ) (fun K => catalanRowSet d K)
    (Classical.decPred (fun K => catalanRowSet d K)) (rowCandidates d)

/-- The associated endpoint set `B_K`. -/
def associatedEndpointSet (d : ℕ) (K : Fin d → ℕ) : Finset ℕ :=
  insert 0 (Finset.univ.image (fun i => K i + 1))

/-- The noncrossing perfect-matching predicate on the endpoint interval. -/
def noncrossingPerfectMatching (d : ℕ)
    (M : Equiv.Perm (Fin (2 * d + 2))) : Prop :=
  (∀ p, M (M p) = p) ∧
    (∀ p, M p ≠ p) ∧
      ∀ p q r s,
        p.1 < r.1 → r.1 < q.1 → q.1 < s.1 →
          M p = q → M r = s → False

/-- The finite carrier of noncrossing perfect matchings. -/
def matchingCandidates (d : ℕ) : Finset (Equiv.Perm (Fin (2 * d + 2))) :=
  @Finset.filter (Equiv.Perm (Fin (2 * d + 2)))
    (fun M => noncrossingPerfectMatching d M)
    (Classical.decPred (fun M => noncrossingPerfectMatching d M)) Finset.univ

/-- The left endpoints of a matching, written as natural numbers. -/
def leftEndpointSet (d : ℕ) (M : Equiv.Perm (Fin (2 * d + 2))) : Finset ℕ :=
  (Finset.univ.filter (fun p => p.1 < (M p).1)).image (fun p => p.1)

/-- The canonical matching whose left endpoints are the associated set. -/
def canonicalMatching (d : ℕ) (K : Fin d → ℕ) : Equiv.Perm (Fin (2 * d + 2)) :=
  if h : ∃ M, M ∈ matchingCandidates d ∧
      leftEndpointSet d M = associatedEndpointSet d K then
    Classical.choose h
  else Equiv.refl (Fin (2 * d + 2))

/-- The signed incidence `ε(B_K,M)`. -/
def cupEpsilon (d : ℕ) (K : Fin d → ℕ)
    (M : Equiv.Perm (Fin (2 * d + 2))) : ℚ :=
  let B := associatedEndpointSet d K
  let selected : Fin (2 * d + 2) → Prop := fun p => p.1 ∈ B
  let balanced : Prop := ∀ p, selected p ↔ ¬ selected (M p)
  let cups := @Finset.filter (Fin (2 * d + 2))
    (fun p => p.1 < (M p).1 ∧ selected p)
    (Classical.decPred
      (fun p => p.1 < (M p).1 ∧ selected p)) Finset.univ
  if balanced then (-1 : ℚ) ^ cups.card else 0

/-- The gauged incidence `W_d(K,M)`. -/
def cupIncidence (d : ℕ) (K : Fin d → ℕ)
    (M : Equiv.Perm (Fin (2 * d + 2))) : ℚ :=
  (-1 : ℚ) ^ (d + 1) * cupEpsilon d K M

/-- The row gauge `S_d(K,K)=(-1)^(|K|-binom d2)`. -/
def rowGauge (d : ℕ) (K : Fin d → ℕ) : ℚ :=
  (-1 : ℚ) ^ ((∑ i : Fin d, K i) - Nat.choose d 2)

/-- The cup-coordinate equation for a polynomial vector, extended by zero
on permutations that are not noncrossing matchings. -/
def cupCoordinateEquation (d : ℕ) (a : Polynomial ℚ)
    (v : Equiv.Perm (Fin (2 * d + 2)) → Polynomial ℚ) : Prop :=
  (∀ K ∈ admissibleRows d,
    Finset.sum (matchingCandidates d) (fun M =>
      Polynomial.C (cupIncidence d K M) * v M) =
      Polynomial.C (rowGauge d K) * flaggedMinor a d K) ∧
    (∀ M, M ∉ matchingCandidates d → v M = 0)

/-- The uniquely determined inverse-cup vector when its exact defining
relations have a unique solution; the zero branch only totalizes the
definition outside that carrier. -/
noncomputable def cupVector (d : ℕ) (a : Polynomial ℚ) :
    Equiv.Perm (Fin (2 * d + 2)) → Polynomial ℚ :=
  if h : ∃! v, cupCoordinateEquation d a v then
    Classical.choose h.exists
  else fun _ => 0

/-- The canonical inverse-cup coordinate indexed by a row set. -/
def cupCoordinate (d : ℕ) (K : Fin d → ℕ) (a : Polynomial ℚ) : Polynomial ℚ :=
  cupVector d a (canonicalMatching d K)

/-- The coefficientwise nonnegative cone `ℚ_{≥0}[b]`. -/
def coefficientwiseNonnegative (p : Polynomial ℚ) : Prop :=
  ∀ i : ℕ, 0 ≤ p.coeff i

/-- Strict positivity on the nonnegative half-shift domain. -/
def strictlyPositiveOnNonnegative (p : Polynomial ℚ) : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    0 < Polynomial.eval x (p.map (algebraMap ℚ ℝ))

/-- Claim 1740: the gauged inverse-cup coordinate for every admissible
 two-row partition is coefficientwise nonnegative and strictly positive for
 every nonnegative half-shift. -/
def completeTwoRowHalfShiftedPositivity_claim1740_repair : Prop :=
  ∀ (d n k : ℕ), 1 ≤ k → k ≤ n → max n (k + 1) ≤ d →
    (∃! v, cupCoordinateEquation d aVariable v) ∧
      coefficientwiseNonnegative
        (cupCoordinate d (twoRowRowSet d n k) aVariable) ∧
      strictlyPositiveOnNonnegative
        (cupCoordinate d (twoRowRowSet d n k) aVariable)

end
end MathlibPlus.Open.Algebra.NewResearch2.C0112Repair
