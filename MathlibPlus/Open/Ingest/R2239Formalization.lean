import Mathlib

namespace MathlibPlus.Open.Ingest.R2239

/-- The primes in the prescribed residue class. -/
def InP (q : ℕ) : Prop :=
  q.Prime ∧ q % 3 = 1

/-- A nonempty increasing tuple of primes from `P`. -/
def ValidTuple (Q : List ℕ) : Prop :=
  Q ≠ [] ∧ Q.Pairwise (· < ·) ∧ ∀ q ∈ Q, InP q

def product (Q : List ℕ) : ℕ := Q.prod

def prefixProduct (Q : List ℕ) (i : ℕ) : ℕ :=
  (Q.take (i + 1)).prod

/-- Resonance between two distinct positions of a finite tuple. -/
def Resonance (Q : List ℕ) : Prop :=
  ∃ i j : Fin Q.length,
    i.val < j.val ∧ Q.get i ∣ Q.get j - 1

/-- The growth inequality at a position for which a successor exists. -/
def Growth (Q : List ℕ) (i : Fin Q.length)
    (h : i.val + 1 < Q.length) : Prop :=
  3 * prefixProduct Q i.val < Q.get ⟨i.val + 1, h⟩

/-- The Dobson arithmetic predicate. -/
def Dobson (Q : List ℕ) : Prop :=
  ValidTuple Q ∧
    ¬ Resonance Q ∧
    ∀ (i : Fin Q.length) (h : i.val + 1 < Q.length), Growth Q i h

/-- A nonempty increasing proper subtuple, expressed without an untyped subset. -/
def ProperSubtuple (R Q : List ℕ) : Prop :=
  R ≠ [] ∧
    R.Pairwise (· < ·) ∧
    (∀ x, x ∈ R → x ∈ Q) ∧
    ∃ x, x ∈ Q ∧ x ∉ R

/-- Inclusion-minimal failure of the Dobson predicate. -/
def MinimalResidual (Q : List ℕ) : Prop :=
  ValidTuple Q ∧
    ¬ Dobson Q ∧
    ∀ R, ProperSubtuple R Q → Dobson R

/-- The two-element arithmetic core condition. -/
def PairCore (Q : List ℕ) : Prop :=
  ∃ p q : ℕ,
    Q = [p, q] ∧
      p < q ∧ InP p ∧ InP q ∧
        (q ≤ 3 * p ∨ p ∣ q - 1)

/-- Characterization of minimal residual tuples of length two. -/
def PairCoreCharacterization : Prop :=
  ∀ Q, MinimalResidual Q → (Q.length = 2 ↔ PairCore Q)

/-- The intermediate growth inequalities, with checked finite indices. -/
def LongIntermediateGrowth (Q : List ℕ) (h : 3 ≤ Q.length) : Prop :=
  ∀ i : Fin (Q.length - 2),
    3 * prefixProduct Q i.val <
      Q.get ⟨i.val + 1, by omega⟩

/-- The final natural-number division bounds. -/
def LongFinalBounds (Q : List ℕ) (h : 3 ≤ Q.length) : Prop :=
  let q₁ : ℕ := Q.get ⟨0, by omega⟩
  let qₛ : ℕ := Q.get ⟨Q.length - 1, by omega⟩
  3 * prefixProduct Q (Q.length - 2) / q₁ < qₛ ∧
    qₛ ≤ 3 * prefixProduct Q (Q.length - 2)

/-- A long-growth core, including the prescribed sorted prime tuple carrier. -/
def LongGrowthCore (Q : List ℕ) : Prop :=
  ValidTuple Q ∧
    3 ≤ Q.length ∧
    (∀ i j : Fin Q.length,
      i.val < j.val → ¬ (Q.get i ∣ Q.get j - 1)) ∧
    (∀ h : 3 ≤ Q.length,
      LongIntermediateGrowth Q h ∧ LongFinalBounds Q h)

/-- Characterization of the long-growth minimal residuals. -/
def LongCoreCharacterization : Prop :=
  ∀ Q, MinimalResidual Q → (3 ≤ Q.length ↔ LongGrowthCore Q)

/-- The explicit retained long-growth example and all its stated arithmetic facts. -/
def RetainedLongGrowthExample : Prop :=
  LongGrowthCore [7, 31, 601] ∧
    product [7, 31, 601] = 130417 ∧
    ¬ Resonance [7, 31, 601] ∧
    3 * 31 < 601 ∧ 601 ≤ 3 * 7 * 31

/-- Products of distinct primes from `P`. -/
def Viable (n : ℕ) : Prop :=
  ∃ Q : List ℕ, ValidTuple Q ∧ product Q = n

/-- The unique increasing `P`-tuple representing a product, when it exists. -/
def CanonicalTuple (Q : List ℕ) (n : ℕ) : Prop :=
  ValidTuple Q ∧
    product Q = n ∧
    ∀ R : List ℕ, ValidTuple R → product R = n → R = Q

/-- The canonical Dobson predicate on a square-free product. -/
def CanonicalDobson (n : ℕ) : Prop :=
  ∃ Q : List ℕ, CanonicalTuple Q n ∧ Dobson Q

/-- A residual square-free product, evaluated on its canonical tuple. -/
def CanonicalResidual (n : ℕ) : Prop :=
  ∃ Q : List ℕ, CanonicalTuple Q n ∧ ¬ Dobson Q

/-- Every canonical residual contains a pair or long-growth arithmetic core. -/
def MinimalCoreDecomposition : Prop :=
  ∀ n, CanonicalResidual n →
    ∃ Q : List ℕ,
      ValidTuple Q ∧ product Q ∣ n ∧
        (PairCore Q ∨ LongGrowthCore Q)

/-- The divisibility closure equality, restricted to the viable carrier. -/
def DivisibilityUpwardClosureEquality : Prop :=
  ∀ n, CanonicalResidual n ↔
    Viable n ∧
      ∃ Q : List ℕ,
        ValidTuple Q ∧
          (PairCore Q ∨ LongGrowthCore Q) ∧ product Q ∣ n

/-- A prime in the congruence class used by the antichain construction. -/
def CongruentPrime (p q : ℕ) : Prop :=
  q.Prime ∧ q % (3 * p) = 1

/-- Dirichlet's infinite antichain assertion together with eventual pair-corehood. -/
def InfiniteArithmeticAntichain : Prop :=
  ∀ p : ℕ,
    InP p →
      Set.Infinite {q : ℕ | CongruentPrime p q} ∧
        ∃ B : ℕ,
          (∀ q : ℕ, B < q → CongruentPrime p q →
            p ∣ q - 1 ∧ PairCore [p, q]) ∧
          (∀ ⦃q r : ℕ⦄,
            B < q → B < r →
              CongruentPrime p q → CongruentPrime p r → q ≠ r →
                p * q ≠ p * r ∧
                  ¬ (p * q ∣ p * r) ∧ ¬ (p * r ∣ p * q))

/-- No finite list of arithmetic cores has the residual divisibility closure. -/
def NoFiniteArithmeticSeedList : Prop :=
  ¬ ∃ F : Finset (List ℕ),
    (∀ Q ∈ F, PairCore Q ∨ LongGrowthCore Q) ∧
      (∀ n : ℕ,
        CanonicalResidual n ↔
          Viable n ∧ ∃ Q ∈ F, product Q ∣ n)

end MathlibPlus.Open.Ingest.R2239
