import Mathlib
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.Combinatorics.R1183ExactCensus

noncomputable section

abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
abbrev State := Equiv.Perm C7
abbrev StateFamily := C7 → State

/-- An offset assignment retains only its support and the values on that
support.  Thus extensions of an offset map away from the support are not
separate assignments. -/
abbrev OffsetAssignment :=
  Σ X : Finset C7, ({x : C7 // x ∈ X} → C7)

abbrev OffsetAssignmentOfSize (k : ℕ) :=
  {q : OffsetAssignment // q.1.card = k}

/-- A point is the least point of a support in the literal order on `Fin 7`. -/
def leastSupportPoint (X : Finset C7) (a : C7) : Prop :=
  a ∈ X ∧ ∀ x : C7, x ∈ X → a ≤ x

/-- Normalization fixes the offset at the least support point and does not
place any coordinates outside the support in the assignment carrier. -/
def normalizedOffsetAssignment (q : OffsetAssignment) : Prop :=
  ∃ a : C7, leastSupportPoint q.1 a ∧
    ∃ ha : a ∈ q.1, q.2 ⟨a, ha⟩ = 0

abbrev NormalizedOffsetAssignment (k : ℕ) :=
  {q : OffsetAssignmentOfSize k // normalizedOffsetAssignment q.1}

def normalizedOffsetAssignments (k : ℕ) : Finset (NormalizedOffsetAssignment k) :=
  letI := Classical.propDecidable
  Finset.univ

def supportOfNormalized (k : ℕ) (q : NormalizedOffsetAssignment k) : Finset C7 :=
  (q.1.1 : OffsetAssignment).1

def offsetOfNormalized (k : ℕ) (q : NormalizedOffsetAssignment k) :
    ({x : C7 // x ∈ supportOfNormalized k q} → C7) :=
  (q.1.1 : OffsetAssignment).2

def affineOffsetAssignment (q : OffsetAssignment) : Prop :=
  ∃ a : C7, leastSupportPoint q.1 a ∧
    ∃ m : C7, ∀ x : C7, ∀ hx : x ∈ q.1,
      q.2 ⟨x, hx⟩ = m * (x - a)

/-- The relative derivative `(∂ᵣδ)(s) = δ(r+s)-δ(r)`. -/
def shiftedRelativeDerivative (r : C7) (δ : State) : C7 → C7 :=
  fun s => δ (r + s) - δ r

/-- A family all of whose states lie in the normalized state space. -/
def normalizedStateFamily (δ : StateFamily) : Prop :=
  ∀ y : C7, δ y ∈ MathlibPlus.Combinatorics.Claim41731.normalizedStates

/-- The six scalar families are the constant families with a scalar state. -/
def constantScalarStateFamily (δ : StateFamily) : Prop :=
  ∃ σ : State,
    σ ∈ MathlibPlus.Combinatorics.Claim41731.scalarStates ∧
      ∀ y : C7, δ y = σ

/-- A nonlinear family contains a normalized state outside the scalar subset. -/
def containsNonlinearState (δ : StateFamily) : Prop :=
  ∃ y : C7,
    δ y ∈ MathlibPlus.Combinatorics.Claim41731.normalizedStates ∧
      δ y ∉ MathlibPlus.Combinatorics.Claim41731.scalarStates

/-- The point-label compatibility equations on a support and its offset map. -/
def compatibleStateFamily (X : Finset C7)
    (r : ({x : C7 // x ∈ X} → C7)) (δ : StateFamily) : Prop :=
  ∀ (x x' : C7) (hx : x ∈ X) (hx' : x' ∈ X) (y : C7),
    shiftedRelativeDerivative (r ⟨x, hx⟩) (δ y) =
      shiftedRelativeDerivative (r ⟨x', hx'⟩) (δ (y + x' - x))

def compatibleFamilies (X : Finset C7)
    (r : ({x : C7 // x ∈ X} → C7)) : Finset StateFamily :=
  letI := Classical.propDecidable
  (Finset.univ : Finset StateFamily).filter (fun δ =>
    normalizedStateFamily δ ∧ compatibleStateFamily X r δ)

def scalarFamilies (X : Finset C7)
    (r : ({x : C7 // x ∈ X} → C7)) : Finset StateFamily :=
  letI := Classical.propDecidable
  (compatibleFamilies X r).filter constantScalarStateFamily

def nonlinearFamilies (X : Finset C7)
    (r : ({x : C7 // x ∈ X} → C7)) : Finset StateFamily :=
  letI := Classical.propDecidable
  (compatibleFamilies X r).filter containsNonlinearState

def normalizedOffsetAssignmentCount (k : ℕ) : ℕ :=
  (normalizedOffsetAssignments k).card

def affineOffsetAssignmentCount (k : ℕ) : ℕ :=
  letI := Classical.propDecidable
  (normalizedOffsetAssignments k).filter (fun q : NormalizedOffsetAssignment k =>
    affineOffsetAssignment (q.1.1 : OffsetAssignment)) |>.card

def scalarFamilyTotal (k : ℕ) : ℕ :=
  Finset.sum (normalizedOffsetAssignments k)
    (fun q : NormalizedOffsetAssignment k =>
      (scalarFamilies (supportOfNormalized k q) (offsetOfNormalized k q)).card)

def nonlinearFamilyTotal (k : ℕ) : ℕ :=
  Finset.sum (normalizedOffsetAssignments k)
    (fun q : NormalizedOffsetAssignment k =>
      (nonlinearFamilies (supportOfNormalized k q) (offsetOfNormalized k q)).card)

/-- Claim 31969. -/
def claim_31969 : Prop :=
  ∀ (q : OffsetAssignment),
    2 ≤ q.1.card →
      normalizedOffsetAssignment q →
        (scalarFamilies q.1 q.2).card = 6 ∧
          ((affineOffsetAssignment q →
              (nonlinearFamilies q.1 q.2).card = 714) ∧
            (¬ affineOffsetAssignment q →
              (nonlinearFamilies q.1 q.2).card = 0))

/-- Claim 31970. -/
def claim_31970 : Prop :=
  normalizedOffsetAssignmentCount 2 = 147 ∧
    affineOffsetAssignmentCount 2 = 147 ∧
      scalarFamilyTotal 2 = 882 ∧ nonlinearFamilyTotal 2 = 104958 ∧
  normalizedOffsetAssignmentCount 3 = 1715 ∧
    affineOffsetAssignmentCount 3 = 245 ∧
      scalarFamilyTotal 3 = 10290 ∧ nonlinearFamilyTotal 3 = 174930 ∧
  normalizedOffsetAssignmentCount 4 = 12005 ∧
    affineOffsetAssignmentCount 4 = 245 ∧
      scalarFamilyTotal 4 = 72030 ∧ nonlinearFamilyTotal 4 = 174930 ∧
  normalizedOffsetAssignmentCount 5 = 50421 ∧
    affineOffsetAssignmentCount 5 = 147 ∧
      scalarFamilyTotal 5 = 302526 ∧ nonlinearFamilyTotal 5 = 104958 ∧
  normalizedOffsetAssignmentCount 6 = 117649 ∧
    affineOffsetAssignmentCount 6 = 49 ∧
      scalarFamilyTotal 6 = 705894 ∧ nonlinearFamilyTotal 6 = 34986 ∧
  normalizedOffsetAssignmentCount 7 = 117649 ∧
    affineOffsetAssignmentCount 7 = 7 ∧
      scalarFamilyTotal 7 = 705894 ∧ nonlinearFamilyTotal 7 = 4998

/-- Claim 31971. -/
def claim_31971 : Prop :=
  Finset.sum (Finset.range 6) (fun j =>
      normalizedOffsetAssignmentCount (j + 2)) = 299586 ∧
    ∀ k : ℕ, 2 ≤ k → k ≤ 7 →
      ∀ (q : NormalizedOffsetAssignment k), q ∈ normalizedOffsetAssignments k →
        ¬ affineOffsetAssignment (q.1.1 : OffsetAssignment) →
          (nonlinearFamilies (supportOfNormalized k q)
            (offsetOfNormalized k q)).card = 0

end

end MathlibPlus.Open.Combinatorics.R1183ExactCensus
