import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The truncated generating polynomial on a valid finite index interval. -/
noncomputable def truncatedIntervalGeneratingPolynomial
    {R : Type*} [CommSemiring R] {n : ℕ}
    (c : Fin n → R) (a b : ℕ) (_ha : a < b) (_hb : b ≤ n) : Polynomial R :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => a ≤ j.1 ∧ j.1 < b),
    Polynomial.C (c j) * Polynomial.X ^ (j.1 - a)

/-- The cut autocorrelation coefficient `[z^(b-a-1)] C_[a,b)(z)^2`. -/
noncomputable def cutAutocorrelationCoefficient_claim4780
    {R : Type*} [CommSemiring R] {n : ℕ}
    (c : Fin n → R) (a b : ℕ) (ha : a < b) (hb : b ≤ n) : R :=
  (truncatedIntervalGeneratingPolynomial c a b ha hb ^ 2).coeff (b - a - 1)

/-- The explicit rank-four wall polynomial from the symbolic certificate. -/
noncomputable def rankFourWallPolynomial : Polynomial ℝ :=
    4096 * Polynomial.X ^ 6
      - 67584 * Polynomial.X ^ 5
      + 449280 * Polynomial.X ^ 4
      - 1562880 * Polynomial.X ^ 3
      + 3049200 * Polynomial.X ^ 2
      - 3243240 * Polynomial.X
      + 1486485

/-- Exact rational brackets replacing the two displayed decimal prefixes. -/
def rankFourNumericalIsolations : Prop :=
  ∃ x y : ℝ,
    0 < x ∧ x < y ∧ y < 4 * Real.pi ∧
    Polynomial.eval x rankFourWallPolynomial = 0 ∧
    Polynomial.eval y rankFourWallPolynomial = 0 ∧
    (16782052469 : ℝ) / 10000000000 < x ∧
      x < (16782052470 : ℝ) / 10000000000 ∧
    (536113359988346505777 : ℝ) / 100000000000000000000 < y ∧
      y < (536113359988346505778 : ℝ) / 100000000000000000000 ∧
    (∀ z : ℝ, 0 < z → Polynomial.eval z rankFourWallPolynomial = 0 → z = x ∨ z = y)

/-- The positive roots have the exact rational isolations represented above. -/
def numericalIsolationsOfTheTwoPositiveRoots_claim4818 : Prop :=
  rankFourNumericalIsolations

abbrev residualGroup (r : ℕ) := (Fin r → ZMod 2) × ZMod 9

def inverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

def cayleyAdjacent {G : Type*} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyGraphsIsomorphic {G : Type*} [AddGroup G]
    (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    cayleyAdjacent S x y ↔ cayleyAdjacent T (e x) (e y)

def cayleyCISet {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ T : Set G,
    T ⊆ {x : G | x ≠ 0} →
    inverseClosed T →
    cayleyGraphsIsomorphic S T →
    ∃ α : G ≃+ G, α '' S = T

/-- Valency-three ordinary undirected CI for `C_2^r × C_9`, including ranks 3, 4, and 5. -/
def c2rTimesC9OrdinaryUndirectedCIValencyThree_claim59849 : Prop :=
  (∀ r : ℕ, ∀ S : Set (residualGroup r),
    S ⊆ {x : residualGroup r | x ≠ 0} →
    S.Finite → S.ncard = 3 → inverseClosed S →
    cayleyCISet S) ∧
  (∀ r : ℕ, (r = 3 ∨ r = 4 ∨ r = 5) →
    ∀ S : Set (residualGroup r),
      S ⊆ {x : residualGroup r | x ≠ 0} →
      S.Finite → S.ncard = 3 → inverseClosed S →
      cayleyCISet S)

end MathlibPlus.Open.ResearchFormalizationBatch
