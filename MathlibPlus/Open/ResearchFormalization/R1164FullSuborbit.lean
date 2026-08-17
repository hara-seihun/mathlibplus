import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
import MathlibPlus.GroupTheory.TwoClosure

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1164

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
open MathlibPlus.GroupTheory.TwoClosure

abbrev R1164F3 := F3
abbrev R1164Plane := F3Square
abbrev R1164Fiber := F3Cube
abbrev R1164Point := RankFiveE
abbrev R1164Row := (R1164Plane → R1164F3) × (R1164Plane → R1164Fiber)
abbrev R1164FiberState := R1164F3 × R1164Fiber

/-- The affine plane terms removed before the retained nonlinear frontier. -/
def r1164AffinePlaneTerm (f : R1164Plane → R1164F3) : Prop :=
  ∃ a b c : R1164F3, ∀ x : R1164Plane,
    f x = c + a * x 0 + b * x 1

/-- Periodicity of a coefficient table in a nonzero plane direction. -/
def r1164CoefficientPeriod (F : R1164Plane → R1164Fiber)
    (k : R1164Plane) : Prop :=
  ∀ x : R1164Plane, F (x + k) = F x

/-- One of the exact corrected affine maps on an 81-point period fibre. -/
def r1164CorrectedFiberStep
    (f : R1164Plane → R1164F3) (F : R1164Plane → R1164Fiber)
    (k s : R1164Plane) (a : R1164FiberState) : R1164FiberState :=
  (a.1 + f (k + s) - f k - f s -
      dot3 (F s) (quadraticIncrement k) + dot3 (F s) a.2,
    a.2 + quadraticIncrement (k + s) - quadraticIncrement k -
      quadraticIncrement s)

/-- The undirected generator relation used for exact fibre components. -/
def r1164CorrectedFiberEdge
    (f : R1164Plane → R1164F3) (F : R1164Plane → R1164Fiber)
    (k : R1164Plane) (a b : R1164FiberState) : Prop :=
  ∃ s : R1164Plane,
    b = r1164CorrectedFiberStep f F k s a ∨
      a = r1164CorrectedFiberStep f F k s b

/-- The exact component of a state under the nine corrected fibre maps. -/
def r1164CorrectedFiberOrbit
    (f : R1164Plane → R1164F3) (F : R1164Plane → R1164Fiber)
    (k : R1164Plane) (a : R1164FiberState) : Set R1164FiberState :=
  {b | Relation.ReflTransGen (r1164CorrectedFiberEdge f F k) a b}

/-- The displayed transporter restricted to the period fibre. -/
def r1164FiberTransporter
    (f : R1164Plane → R1164F3) (k : R1164Plane)
    (a : R1164FiberState) : R1164FiberState :=
  (a.1 + f k, a.2 + quadraticIncrement k)

/-- The exact corrected-local orbit-fixation test used to remove rows. -/
def r1164CorrectedLocalFixation
    (f : R1164Plane → R1164F3) (F : R1164Plane → R1164Fiber)
    (k : R1164Plane) : Prop :=
  ∀ a : R1164FiberState,
    r1164FiberTransporter f k a ∈ r1164CorrectedFiberOrbit f F k a

/-- The retained rows are the normalized nonlinear rows failing a period-fibre
    corrected-local test. -/
def r1164RetainedRowPredicate
    (f : R1164Plane → R1164F3) (F : R1164Plane → R1164Fiber) : Prop :=
  f 0 = 0 ∧
    F 0 = 0 ∧
      ¬ r1164AffinePlaneTerm f ∧
        ¬ (∀ x : R1164Plane, F x = F 0) ∧
          ∃ k : R1164Plane,
            k ≠ 0 ∧
              r1164CoefficientPeriod F k ∧
                ¬ r1164CorrectedLocalFixation f F k

abbrev R1164RetainedRow :=
  {r : R1164Row // r1164RetainedRowPredicate r.1 r.2}

def r1164DisplayedTransporter (r : R1164RetainedRow) : Equiv.Perm R1164Point :=
  rankFiveQuadraticTransporterPerm r.1.1 r.1.2

def r1164GeneratedGroup (r : R1164RetainedRow) :
    Subgroup (Equiv.Perm R1164Point) :=
  rankFivePairGroup r.1.1 r.1.2

def r1164PointStabilizerOrbit (r : R1164RetainedRow)
    (x : R1164Point) : Set R1164Point :=
  pointStabilizerOrbit (r1164GeneratedGroup r) rankFiveZero x

def r1164MovedSuborbit (r : R1164RetainedRow) : Prop :=
  ∃ x : R1164Point,
    Set.image (r1164DisplayedTransporter r) (r1164PointStabilizerOrbit r x) ≠
      r1164PointStabilizerOrbit r x

def r1164DisplayedClosureFailure (r : R1164RetainedRow) : Prop :=
  ¬ inTwoClosure (r1164GeneratedGroup r) (r1164DisplayedTransporter r)

def r1164GeneratedGroupOrder (r : R1164RetainedRow) : ℕ :=
  Nat.card (r1164GeneratedGroup r)

def r1164PointStabilizerOrbitFamily (r : R1164RetainedRow) : Set (Set R1164Point) :=
  Set.range (r1164PointStabilizerOrbit r)

def r1164PointStabilizerOrbitCount (r : R1164RetainedRow) : ℕ :=
  Set.ncard (r1164PointStabilizerOrbitFamily r)

def r1164CoefficientImageRank (r : R1164RetainedRow) : ℕ :=
  Module.finrank R1164F3
    (Submodule.span R1164F3 (Set.range r.1.2))

def r1164RetainedCount : ℕ :=
  Nat.card R1164RetainedRow

def r1164CensusClass (groupOrder orbitCount imageRank : ℕ) : Set R1164RetainedRow :=
  {r | r1164GeneratedGroupOrder r = groupOrder ∧
    r1164PointStabilizerOrbitCount r = orbitCount ∧
      r1164CoefficientImageRank r = imageRank}

def r1164CensusClassCount (groupOrder orbitCount imageRank : ℕ) : ℕ :=
  Set.ncard (r1164CensusClass groupOrder orbitCount imageRank)

def r1164ImageRankCount (imageRank : ℕ) : ℕ :=
  Set.ncard {r : R1164RetainedRow | r1164CoefficientImageRank r = imageRank}

/-- Claim 41498: every retained displayed transporter moves a point-stabilizer
    suborbit and is consequently outside the generated exact 2-closure. -/
def claim41498 : Prop :=
  r1164RetainedCount = 50262 ∧
    ∀ r : R1164RetainedRow,
      r1164MovedSuborbit r ∧ r1164DisplayedClosureFailure r

/-- Claim 41499: the complete generated-group and suborbit census on the
    retained nonlinear frontier. -/
def claim41499 : Prop :=
  r1164RetainedCount = 50262 ∧
    r1164CensusClassCount (3 ^ 9) 81 1 = 7062 ∧
      r1164CensusClassCount (3 ^ 11) 73 1 = 11520 ∧
        r1164CensusClassCount (3 ^ 11) 61 2 = 31680 ∧
          r1164ImageRankCount 1 = 18582 ∧
            r1164ImageRankCount 2 = 31680 ∧
              r1164CensusClassCount (3 ^ 9) 81 1 +
                  r1164CensusClassCount (3 ^ 11) 73 1 +
                    r1164CensusClassCount (3 ^ 11) 61 2 =
                r1164RetainedCount ∧
                ∀ r : R1164RetainedRow,
                  r1164DisplayedClosureFailure r

/-- Claim 41500: the displayed-transporter suborbit-fixation route has no
    successful row on this exact retained frontier. -/
def claim41500 : Prop :=
  r1164RetainedCount = 50262 ∧
    (¬ ∃ r : R1164RetainedRow,
      ¬ r1164DisplayedClosureFailure r) ∧
      ∀ r : R1164RetainedRow, r1164DisplayedClosureFailure r

end MathlibPlus.Open.ResearchFormalization.R1164
