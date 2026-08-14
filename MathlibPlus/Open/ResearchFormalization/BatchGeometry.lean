import Mathlib

noncomputable section
open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization

/-! Exact geometric carriers and statements for the admitted R-3332 setup. -/

abbrev Point (n : ℕ) := Fin n → EuclideanSpace ℝ (Fin 2)
abbrev VectorConfiguration (n : ℕ) := Point n

/-- The ordered unequal pairs, used when taking the minimum pairwise distance. -/
def PairIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

def pointDistance {n : ℕ} (x : Point n) (i j : Fin n) : ℝ :=
  ‖x i - x j‖

def minimumPairwiseDistance {n : ℕ} (x : Point n) : ℝ :=
  sInf (Set.range (fun p : PairIndex n => pointDistance x p.1.1 p.1.2))

def diameter {n : ℕ} (x : Point n) : ℝ :=
  sSup (Set.range (fun p : Fin n × Fin n => pointDistance x p.1 p.2))

def unitSeparated {n : ℕ} (x : Point n) : Prop :=
  ∀ i j : Fin n, i ≠ j → 1 ≤ pointDistance x i j

def minimumDiameter (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ x : Point n, unitSeparated x ∧ diameter x = d}

def globalMinimumDiameter (n : ℕ) (x : Point n) : Prop :=
  unitSeparated x ∧
    ∀ y : Point n, unitSeparated y → diameter x ≤ diameter y

/-- The minimum is represented by an infimum together with an explicit
attainment/global-lower-bound premise, rather than by an unqualified infimum. -/
def exactMinimizer (n : ℕ) (x : Point n) : Prop :=
  2 ≤ n ∧
  unitSeparated x ∧
  minimumPairwiseDistance x = 1 ∧
  diameter x = minimumDiameter n ∧
  globalMinimumDiameter n x

def contactEdge {n : ℕ} (x : Point n) (i j : Fin n) : Prop :=
  i ≠ j ∧ pointDistance x i j = 1

def diameterEdge {n : ℕ} (x : Point n) (i j : Fin n) : Prop :=
  i ≠ j ∧ pointDistance x i j = diameter x

def containsAllDiameterEndpoints {n : ℕ}
    (x : Point n) (B : Finset (Fin n)) : Prop :=
  ∀ i j, diameterEdge x i j → i ∈ B ∧ j ∈ B

def perturbation {n : ℕ}
    (x : Point n) (w : VectorConfiguration n) (t : ℝ) : Point n :=
  fun i => x i + t • w i

def endpointPinnedFlex {n : ℕ}
    (x : Point n) (B : Finset (Fin n)) : Set (VectorConfiguration n) :=
  {w |
    (∀ b, b ∈ B → w b = 0) ∧
    (∀ i j, contactEdge x i j →
      inner ℝ (x i - x j) (w i - w j) = 0)}

def universallyFixedOnFlex {n : ℕ}
    (x : Point n) (B : Finset (Fin n)) (i j : Fin n) : Prop :=
  ∀ w ∈ endpointPinnedFlex x B, w i - w j = 0

def contactFixedOnFlexSet {n : ℕ}
    (x : Point n) (B : Finset (Fin n)) (i j : Fin n) :
    Set (VectorConfiguration n) :=
  {w | w ∈ endpointPinnedFlex x B ∧ w i - w j = 0}

/-- The definition is accompanied by the exact subspace interface for F_B
and each contact kernel K_e; the witnesses are constrained by the displayed
sets rather than being opaque replacement carriers. -/
def endpointPinnedFlexLinearInterface : Prop :=
  ∀ (n : ℕ) (x : Point n) (B : Finset (Fin n)),
    (∃ F : Submodule ℝ (VectorConfiguration n),
      ∀ w, w ∈ F ↔ w ∈ endpointPinnedFlex x B) ∧
    (∀ i j, contactEdge x i j →
      ∃ K : Submodule ℝ (VectorConfiguration n),
        ∀ w, w ∈ K ↔ w ∈ contactFixedOnFlexSet x B i j)

/-- Feasibility spells out the three finite-pair behaviours in the packet:
strict inactive margins, nondecreasing contacts, fixed diameter pairs, and the
resulting pairwise lower/upper bounds. -/
def locallyFeasible {n : ℕ}
    (x : Point n) (w : VectorConfiguration n) (t : ℝ) : Prop :=
  let xt := perturbation x w t
  (∀ i j, i ≠ j →
    (¬ contactEdge x i j ∧ ¬ diameterEdge x i j) →
      1 < pointDistance xt i j ∧ pointDistance xt i j < diameter x) ∧
  (∀ i j, contactEdge x i j → 1 ≤ pointDistance xt i j) ∧
  (∀ i j, diameterEdge x i j → pointDistance xt i j = diameter x) ∧
  (∀ i j, i ≠ j → 1 ≤ pointDistance xt i j ∧ pointDistance xt i j ≤ diameter x)

def localPinnedFlexFeasibility : Prop :=
  ∀ (n : ℕ) (x : Point n) (B : Finset (Fin n))
    (w : VectorConfiguration n),
    exactMinimizer n x →
    w ∈ endpointPinnedFlex x B →
    containsAllDiameterEndpoints x B →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, |t| < ε → locallyFeasible x w t

def endpointPinnedContactFlexDichotomy : Prop :=
  ∀ (n : ℕ) (x : Point n) (B : Finset (Fin n)),
    exactMinimizer n x →
    containsAllDiameterEndpoints x B →
    (endpointPinnedFlex x B = ({0} : Set (VectorConfiguration n))) ∨
      ∃ i j : Fin n,
        contactEdge x i j ∧ universallyFixedOnFlex x B i j

end MathlibPlus.Open.ResearchFormalization
