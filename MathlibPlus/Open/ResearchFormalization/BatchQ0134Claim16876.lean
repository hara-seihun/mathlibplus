import MathlibPlus.Open.ResearchFormalization.Q0134GoodBad

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16876

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879
open scoped BigOperators

/-- An indexed list of centers enumerates exactly the physical point set. -/
def enumeratesPointSet {n : ℕ} (P : Finset Plane)
    (centers : Fin n → Plane) : Prop :=
  (∀ i, centers i ∈ P) ∧
    (∀ v, v ∈ P → ∃! i : Fin n, centers i = v)

/-- Each indexed center chooses four points from one positive centered circle. -/
def witnessFamily {n : ℕ} (P : Finset Plane)
    (centers : Fin n → Plane) (radii : Fin n → ℝ)
    (Q : Fin n → Finset Plane) : Prop :=
  enumeratesPointSet P centers ∧
    ∀ i, 0 < radii i ∧
      selectedFourPointWitness P (centers i) (radii i) (Q i)

/-- The incidence degree of a physical point in the chosen four-sets. -/
noncomputable def incidenceDegree {n : ℕ}
    (Q : Fin n → Finset Plane) (v : Plane) : ℕ :=
  Fintype.card {i : Fin n // v ∈ Q i}

/-- The cardinality of the common physical-point set of two chosen blocks. -/
noncomputable def commonPointCount {n : ℕ}
    (Q : Fin n → Finset Plane) (i j : Fin n) : ℕ :=
  Set.ncard ((Q i : Set Plane) ∩ (Q j : Set Plane))

/-- The sum of the pairwise block intersections, indexed by `i < j`. -/
noncomputable def pairIntersectionSum {n : ℕ}
    (Q : Fin n → Finset Plane) : ℕ :=
  ∑ i : Fin n, (∑ j ∈ Finset.Ioi i, commonPointCount Q i j)

/-- The first and second incidence sums in the counting argument. -/
noncomputable def incidenceDegreeSum {n : ℕ} (P : Finset Plane)
    (Q : Fin n → Finset Plane) : ℕ :=
  ∑ v ∈ P, incidenceDegree Q v

noncomputable def incidenceBinomialSum {n : ℕ} (P : Finset Plane)
    (Q : Fin n → Finset Plane) : ℕ :=
  ∑ v ∈ P, Nat.choose (incidenceDegree Q v) 2

/-- Two different centered circles meet in at most two selected physical points. -/
def distinctCircleIntersectionBound {n : ℕ}
    (centers : Fin n → Plane) (radii : Fin n → ℝ)
    (Q : Fin n → Finset Plane) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    (centers i, radii i) ≠ (centers j, radii j) →
      commonPointCount Q i j ≤ 2

/-- The equality fixture described as the `2-(7,4,2)` incidence design. -/
def incidenceDesign742 {n : ℕ} (P : Finset Plane)
    (Q : Fin n → Finset Plane) : Prop :=
  P.card = 7 ∧ n = 7 ∧
    (∀ i, (Q i).card = 4) ∧
    (∀ v, v ∈ P → incidenceDegree Q v = 4) ∧
    (∀ i j : Fin n, i ≠ j → commonPointCount Q i j = 2)

/-- All geometric and counting conclusions for one faithful witness family. -/
def elementaryCountingConclusion {n : ℕ} (P : Finset Plane)
    (centers : Fin n → Plane) (radii : Fin n → ℝ)
    (Q : Fin n → Finset Plane) : Prop :=
  distinctCircleIntersectionBound centers radii Q ∧
    incidenceDegreeSum P Q = 4 * n ∧
    incidenceBinomialSum P Q = pairIntersectionSum Q ∧
    pairIntersectionSum Q ≤ 2 * Nat.choose n 2 ∧
    6 * n ≤ incidenceBinomialSum P Q ∧
    7 ≤ n ∧
    (n = 7 → incidenceDesign742 P Q)

/-- Claim 16876: the centered-circle incidence count, its Cauchy lower bound,
its bad-configuration consequence, and the equality design are all retained on
 the physical planar carrier. -/
def claim16876 : Prop :=
  ∀ P : Finset Plane, Q0134GoodBad.badConfiguration P →
    (∀ n : ℕ, ∀ centers : Fin n → Plane, ∀ radii : Fin n → ℝ,
      ∀ Q : Fin n → Finset Plane,
        P.card = n → witnessFamily P centers radii Q →
          elementaryCountingConclusion P centers radii Q) ∧
    7 ≤ P.card ∧
    ∃ centers : Fin P.card → Plane, ∃ radii : Fin P.card → ℝ,
      ∃ Q : Fin P.card → Finset Plane,
        witnessFamily P centers radii Q ∧
          (P.card = 7 → incidenceDesign742 P Q)

end

end MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16876
