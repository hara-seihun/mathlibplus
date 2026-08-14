import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0498

open scoped BigOperators
noncomputable section

/-- The q-integer attached to a positive leg length. -/
def qInteger (a : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range a, (Polynomial.X : Polynomial ℚ) ^ i

/-- The product of q-integers attached to a finite multiset of leg lengths. -/
def qIntegerProduct (s : Multiset ℕ) : Polynomial ℚ :=
  (s.map qInteger).prod

/-- Positivity of every member of a leg-length multiset. -/
def PositiveLegMultiset (s : Multiset ℕ) : Prop :=
  ∀ a, a ∈ s → 0 < a

/-- Equality of q-integer products recovers all leg lengths at least two; length one
legs remain invisible. -/
def qIntegerProductRecoversNonunitLegLengths : Prop :=
  (∀ s t : Multiset ℕ,
    PositiveLegMultiset s →
    PositiveLegMultiset t →
    qIntegerProduct s = qIntegerProduct t →
    ∀ n : ℕ, 2 ≤ n → Multiset.count n s = Multiset.count n t) ∧
  qInteger 1 = 1

/-- Nonnegative triples summing to N, with the finite bound supplied by the sum. -/
def ThreePart (N : ℕ) :=
  {μ : Fin 3 → Fin (N + 1) // ∑ i : Fin 3, (μ i).val = N}

instance threePartFintype (N : ℕ) : Fintype (ThreePart N) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun μ : Fin 3 → Fin (N + 1) =>
      ∑ i : Fin 3, (μ i).val = N))
    (by intro μ; simp)

def blockX : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0

def blockQ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1

def threeFactorSum (N : ℕ) (t : ThreePart N) : MvPolynomial (Fin 2) ℚ :=
  blockQ ^ (t.1 0).val + blockQ ^ (t.1 1).val + blockQ ^ (t.1 2).val

def threeFactorProduct (N : ℕ) (t : ThreePart N) : MvPolynomial (Fin 2) ℚ :=
  ∏ i : Fin 3, (1 + blockX * blockQ ^ (t.1 i).val)

def threeFactorReciprocalForm (N : ℕ) (t : ThreePart N) : MvPolynomial (Fin 2) ℚ :=
  1 + blockX * threeFactorSum N t +
    blockX ^ 2 * blockQ ^ N *
      (blockQ ^ (N - (t.1 0).val) +
        blockQ ^ (N - (t.1 1).val) +
        blockQ ^ (N - (t.1 2).val)) +
    blockX ^ 3 * blockQ ^ N

/-- The reciprocal block expansion and the exact equivalence of its linear
relations with those of the three-term reciprocal blocks. -/
def threeFactorReciprocalBlockReduction : Prop :=
  ∀ N : ℕ,
    (∀ t : ThreePart N,
      threeFactorProduct N t = threeFactorReciprocalForm N t) ∧
    (∀ r : ThreePart N → ℚ,
      (∑ t : ThreePart N, r t • threeFactorProduct N t = 0) ↔
      (∑ t : ThreePart N, r t • threeFactorSum N t = 0))

end

end MathlibPlus.Open.ResearchFormalization.R0498
