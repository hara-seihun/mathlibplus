import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim26123

/-- A side of a double spider is a finite positive multiset of leg lengths. -/
def positiveLegMultiset (A : Multiset ℕ) : Prop :=
  ∀ a, a ∈ A → 0 < a

/-- Disjointness here is disjointness of leg-length occurrences as multisets. -/
def disjointLegMultisets (A A' : Multiset ℕ) : Prop :=
  ∀ a, a ∈ A → a ∉ A'

structure DoubleSpider where
  smaller : Multiset ℕ
  trunk : ℕ
  larger : Multiset ℕ

def validDoubleSpider (T : DoubleSpider) : Prop :=
  positiveLegMultiset T.smaller ∧
    positiveLegMultiset T.larger ∧
    2 ≤ T.smaller.card ∧ 2 ≤ T.larger.card ∧ 1 ≤ T.trunk

def unitGapCandidate (A A' : Multiset ℕ) (c : ℕ) : DoubleSpider :=
  { smaller := A
    trunk := c
    larger := A' + ({1} : Multiset ℕ) }

/-- Claim 26123: when the smaller two-leg sum is one below the larger
    total, two distinct eligible two-leg submultisets are disjoint, the
    global leg multiset consists of those four legs and one unit leg, and
    the only oriented double-spider candidates are the two unit transfers. -/
def unitGapAmbiguityClassification_claim26123 : Prop :=
  ∀ (A A' C : Multiset ℕ) (α c : ℕ),
    positiveLegMultiset A →
    positiveLegMultiset A' →
    positiveLegMultiset C →
    A.card = 2 →
    A'.card = 2 →
    A.sum = α →
    A'.sum = α →
    A ≤ C →
    A' ≤ C →
    A ≠ A' →
    C.sum = α + (α + 1) →
    2 ≤ c →
    disjointLegMultisets A A' ∧
      C = A + A' + ({1} : Multiset ℕ) ∧
      C.card = 5 ∧
      (∀ T : DoubleSpider,
        validDoubleSpider T →
        T.trunk = c →
        T.smaller.card = 2 →
        T.smaller.sum = α →
        T.larger.sum = α + 1 →
        T.smaller + T.larger = C →
        T.larger.card = 3 ∧
          (T = unitGapCandidate A A' c ∨
            T = unitGapCandidate A' A c))

end MathlibPlus.Open.ResearchFormalization.Claim26123
