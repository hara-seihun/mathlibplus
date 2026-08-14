import Mathlib

namespace MathlibPlus.Open.Research.BatchQ0060

noncomputable section

/-- Normalized Hamming distance: the fraction of points moved differently. -/
def normalizedHamming
    {X : Type*} [Fintype X] [DecidableEq X]
    (σ τ : Equiv.Perm X) : ℝ :=
  ((Finset.univ.filter (fun x : X => σ x ≠ τ x)).card : ℝ) /
    (Fintype.card X : ℝ)

/-- A finite presentation by finite indexed generators and relator words. -/
structure FinitePermutationPresentation where
  generators : ℕ
  relators : ℕ
  relator : Fin relators → List (Fin generators × Bool)

def evaluateSignedWord
    {g n : ℕ}
    (σ : Fin g → Equiv.Perm (Fin n)) :
    List (Fin g × Bool) → Equiv.Perm (Fin n)
  | [] => 1
  | (i, inverse)::word =>
      (if inverse then (σ i)⁻¹ else σ i) * evaluateSignedWord σ word

def relatorPermutation
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ : Fin P.generators → Equiv.Perm (Fin n))
    (r : Fin P.relators) : Equiv.Perm (Fin n) :=
  evaluateSignedWord σ (P.relator r)

def exactPermutationSolution
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ : Fin P.generators → Equiv.Perm (Fin n)) : Prop :=
  ∀ r, relatorPermutation P σ r = 1

def localRelatorDefectSum
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ : Fin P.generators → Equiv.Perm (Fin n)) : ℝ :=
  ∑ r : Fin P.relators, normalizedHamming (relatorPermutation P σ r) 1

def localRelatorDefectAverage
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ : Fin P.generators → Equiv.Perm (Fin n)) : ℝ :=
  localRelatorDefectSum P σ / (P.relators : ℝ)

def assignmentDistanceSum
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ τ : Fin P.generators → Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin P.generators, normalizedHamming (σ i) (τ i)

def assignmentDistanceAverage
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ τ : Fin P.generators → Equiv.Perm (Fin n)) : ℝ :=
  assignmentDistanceSum P σ τ / (P.generators : ℝ)

def strictRepairDefect
    (P : FinitePermutationPresentation) {n : ℕ}
    (σ : Fin P.generators → Equiv.Perm (Fin n)) : ℝ :=
  sInf {d : ℝ |
    ∃ τ : Fin P.generators → Equiv.Perm (Fin n),
      exactPermutationSolution P τ ∧ d = assignmentDistanceAverage P σ τ}

/-- The local and strict global defect conventions for a finite presentation. -/
def normalizedPermutationDefects : Prop :=
  ∀ (P : FinitePermutationPresentation) (n : ℕ),
    0 < n →
    ∀ σ : Fin P.generators → Equiv.Perm (Fin n),
      localRelatorDefectSum P σ =
          (P.relators : ℝ) * localRelatorDefectAverage P σ ∧
      (∀ τ : Fin P.generators → Equiv.Perm (Fin n),
        assignmentDistanceSum P σ τ =
          (P.generators : ℝ) * assignmentDistanceAverage P σ τ) ∧
      (∃ τ : Fin P.generators → Equiv.Perm (Fin n),
        exactPermutationSolution P τ ∧
        strictRepairDefect P σ = assignmentDistanceAverage P σ τ ∧
        ∀ υ : Fin P.generators → Equiv.Perm (Fin n),
          exactPermutationSolution P υ →
            assignmentDistanceAverage P σ τ ≤
              assignmentDistanceAverage P σ υ)

def goodCore
    {G X : Type*} [Group G]
    (Φ : G → Equiv.Perm X) : Set X :=
  {x | ∀ g h : G, Φ g (Φ h x) = Φ (g * h) x}

def relationViolationMass
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X]
    (Φ : G → Equiv.Perm X) (g h : G) : ℝ :=
  normalizedHamming (Φ g * Φ h) (Φ (g * h))

def totalRelationViolationMass
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
      [DecidableEq G] [DecidableEq X]
    (Φ : G → Equiv.Perm X) : ℝ :=
  ∑ g : G, ∑ h : G, relationViolationMass Φ g h

def averageRelationViolationMass
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
      [DecidableEq G] [DecidableEq X]
    (Φ : G → Equiv.Perm X) : ℝ :=
  totalRelationViolationMass Φ / (Fintype.card G : ℝ) ^ 2

def badPointMass
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
      [DecidableEq G] [DecidableEq X]
    (Φ : G → Equiv.Perm X) : ℝ := by
  classical
  exact
    ((Finset.univ.filter (fun x : X => x ∉ goodCore Φ)).card : ℝ) /
      (Fintype.card X : ℝ)

def restrictedGoodCoreAction
    {G X : Type*} [Group G]
    (Φ : G → Equiv.Perm X) : Prop :=
  (∀ x : X, x ∈ goodCore Φ → Φ 1 x = x) ∧
  (∀ g h : G, ∀ x : X, x ∈ goodCore Φ →
    Φ g (Φ h x) = Φ (g * h) x)

def repairDistance
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
      [DecidableEq G] [DecidableEq X]
    (Φ τ : G → Equiv.Perm X) : ℝ :=
  (∑ g : G, normalizedHamming (Φ g) (τ g)) / (Fintype.card G : ℝ)

/-- The good-core construction, its exact repair, and its union-bound estimates. -/
def goodCoreStrictRepair
    (G X : Type*) [Group G] [Fintype G] [Fintype X]
      [DecidableEq G] [DecidableEq X] [Nonempty X]
    (Φ : G → Equiv.Perm X) : Prop :=
  (∀ g : G, ∀ x : X,
    x ∈ goodCore Φ ↔ Φ g x ∈ goodCore Φ) ∧
  restrictedGoodCoreAction Φ ∧
  badPointMass Φ ≤ totalRelationViolationMass Φ ∧
  badPointMass Φ ≤ (Fintype.card G : ℝ) ^ 2 * averageRelationViolationMass Φ ∧
  (∃ τ : G → Equiv.Perm X,
    (∀ g h : G, τ g * τ h = τ (g * h)) ∧
    (∀ x : X, τ 1 x = x) ∧
    (∀ g : G, ∀ x : X, x ∈ goodCore Φ → τ g x = Φ g x) ∧
    (∀ g : G, ∀ x : X, x ∉ goodCore Φ → τ g x = x) ∧
    repairDistance Φ τ ≤ badPointMass Φ)

def cycleLengthDoesNotDivide
    {X : Type*} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) (m : ℕ) (x : X) : Prop :=
  ∃ k : ℕ,
    0 < k ∧
    (σ ^ k) x = x ∧
    (∀ j : ℕ, 0 < j → (σ ^ j) x = x → k ≤ j) ∧
    ¬ k ∣ m

def cycleBadPointMass
    {X : Type*} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) (m : ℕ) : ℝ := by
  classical
  exact
    ((Finset.univ.filter (fun x : X => cycleLengthDoesNotDivide σ m x)).card : ℝ) /
      (Fintype.card X : ℝ)

def onePowerLocalDefect
    {X : Type*} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) (m : ℕ) : ℝ :=
  normalizedHamming (σ ^ m) 1

/-- The exact cycle repair for the one-power presentation. -/
def onePowerRelationLinearStrictRepair
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] : Prop :=
  ∀ m : ℕ, 0 < m →
    ∀ σ : Equiv.Perm X,
      onePowerLocalDefect σ m = cycleBadPointMass σ m ∧
      ∃ τ : Equiv.Perm X,
        τ ^ m = 1 ∧
        (∀ x : X, (σ ^ m) x = x → τ x = σ x) ∧
        (∀ x : X, (σ ^ m) x ≠ x → τ x = x) ∧
        normalizedHamming σ τ ≤ onePowerLocalDefect σ m

def almostCommutingPermutationsAreRepairable : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, 0 < n →
      ∀ σ : Fin k → Equiv.Perm (Fin n),
        (∀ i j : Fin k,
          normalizedHamming (σ i * σ j) (σ j * σ i) < δ) →
        ∃ τ : Fin k → Equiv.Perm (Fin n),
          (∀ i j : Fin k, τ i * τ j = τ j * τ i) ∧
          (∀ i : Fin k, normalizedHamming (σ i) (τ i) < ε)

end

end MathlibPlus.Open.Research.BatchQ0060
