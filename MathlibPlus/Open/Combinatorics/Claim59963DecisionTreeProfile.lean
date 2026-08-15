import Mathlib

noncomputable section

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance classicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A Boolean encoding of the cube `{-1,1}^S`. -/
abbrev SpinCube (S : Type*) := S → Bool

/-- The value in `{-1,1}` represented by a Boolean coordinate. -/
def spinValue (b : Bool) : ℝ := if b then 1 else -1

/-- A finite deterministic binary decision tree. -/
inductive DecisionTree (S : Type*) where
  | leaf : ℝ → DecisionTree S
  | branch : S → DecisionTree S → DecisionTree S → DecisionTree S

/-- The depth of a binary decision tree. -/
def DecisionTree.depth {S : Type*} : DecisionTree S → ℕ
  | .leaf _ => 0
  | .branch _ left right => 1 + max left.depth right.depth

/-- Evaluation of a binary decision tree on the Boolean cube. -/
def DecisionTree.eval {S : Type*} : DecisionTree S → SpinCube S → ℝ
  | .leaf value, _ => value
  | .branch coordinate left right, x =>
      if x coordinate then right.eval x else left.eval x

/-- A partial Boolean assignment and its unassigned-coordinate type. -/
abbrev PartialAssignment (S : Type*) := S → Option Bool

abbrev FreeCoordinates {S : Type*} (ρ : PartialAssignment S) :=
  {i : S // ρ i = none}

instance instFintypeFreeCoordinates {S : Type*} [Fintype S]
    (ρ : PartialAssignment S) : Fintype (FreeCoordinates ρ) :=
  Fintype.ofFinite _

/-- Fill the assigned coordinates of `ρ` and leave the free coordinates to `x`. -/
def extendAssignment {S : Type*} (ρ : PartialAssignment S)
    (x : SpinCube (FreeCoordinates ρ)) : SpinCube S :=
  fun i =>
    match h : ρ i with
    | some b => b
    | none => x ⟨i, h⟩

/-- The normalized clamped derivative in one free coordinate. -/
def clampedDerivative {S : Type*} [Fintype S]
    (i : S) (g : SpinCube S → ℝ) (x : SpinCube S) : ℝ :=
  (g (fun j => if j = i then true else x j) -
      g (fun j => if j = i then false else x j)) / 2

/-- Clamp every coordinate in `U` according to a Boolean assignment on `U`. -/
def clampOn {S : Type*} (x : SpinCube S) (U : Finset S)
    (σ : U → Bool) : SpinCube S :=
  fun j => if h : j ∈ U then σ ⟨j, h⟩ else x j

/-- The product of the normalized clamped derivatives on a finite coordinate set.

This is the order-independent alternating-sum expansion of `∏ i∈U D_i`. -/
def clampedDerivativeSet {S : Type*} [Fintype S]
    (U : Finset S) (g : SpinCube S → ℝ) (x : SpinCube S) : ℝ :=
  (1 / (2 : ℝ) ^ U.card) *
    ∑ σ : U → Bool,
      (∏ i : U, spinValue (σ i)) * g (clampOn x U σ)

/-- Uniform expectation on a finite Boolean cube. -/
def cubeExpectation {S : Type*} [Fintype S]
    (g : SpinCube S → ℝ) : ℝ :=
  (∑ x : SpinCube S, g x) / (Fintype.card (SpinCube S) : ℝ)

/-- The coefficient of order `m` in the L1 derivative profile. -/
def firstDerivativeProfile {S : Type*} [Fintype S]
    (m : ℕ) (g : SpinCube S → ℝ) : ℝ :=
  ∑ U : Finset S,
    if U.card = m then
      cubeExpectation (fun x => |clampedDerivativeSet U g x|)
    else 0

/-- The derivative-profile generating function. -/
def derivativeProfileGenerating {S : Type*} [Fintype S]
    (t : ℝ) (g : SpinCube S → ℝ) : ℝ :=
  ∑ U : Finset S,
    t ^ U.card * cubeExpectation (fun x => |clampedDerivativeSet U g x|)

/-- The depth-scale logarithm. -/
def depthScale {S : Type*} [Fintype S]
    (t : ℝ) (g : SpinCube S → ℝ) : ℝ :=
  Real.log (max 1 (derivativeProfileGenerating t g)) / Real.log (1 + t)

/-- The parity on the distinct coordinates in `U`. -/
def coordinateParity {S : Type*} [Fintype S] (U : Finset S)
    (x : SpinCube S) : ℝ :=
  ∏ i : U, spinValue (x i)

/-- Claim 59963: decision-tree depth controls every conditioned L1 derivative
profile, with the stated convexity and sharpness assertions. -/
def claim59963_decisionTreeDerivativeProfile : Prop :=
  ∀ {S A : Type*} [Fintype S] [Fintype A],
    ∀ (T : A → SpinCube S → ℝ)
      (weights : A → ℝ)
      (k : A → ℕ)
      (trees : ∀ a, DecisionTree S),
      (∀ a x, -1 ≤ T a x ∧ T a x ≤ 1) →
      (∀ a x, (trees a).eval x = T a x) →
      (∀ a, (trees a).depth ≤ k a) →
      (∀ a, 0 ≤ weights a) →
      (∑ a, weights a = 1) →
      ∀ ρ : PartialAssignment S,
        let F := FreeCoordinates ρ
        let fρ : SpinCube F → ℝ :=
          fun x => ∑ a, weights a * T a (extendAssignment ρ x)
        (∀ m : ℕ,
            firstDerivativeProfile m fρ ≤
              ∑ a, weights a * Nat.choose (k a) m) ∧
          (∀ t : ℝ, 0 ≤ t →
            derivativeProfileGenerating t fρ ≤
              ∑ a, weights a * (1 + t) ^ k a) ∧
          (∀ t : ℝ, 0 ≤ t →
            ConvexOn ℝ Set.univ
              (fun g : SpinCube F → ℝ => derivativeProfileGenerating t g)) ∧
          (∀ k₀ : ℕ,
            (∀ a, k a ≤ k₀) →
              (∀ m : ℕ,
                  firstDerivativeProfile m fρ ≤ Nat.choose k₀ m) ∧
                (∀ t : ℝ, 0 ≤ t →
                  derivativeProfileGenerating t fρ ≤ (1 + t) ^ k₀) ∧
                (∀ t : ℝ, 0 < t → depthScale t fρ ≤ k₀)) ∧
          (∀ (U : Finset F) (m : ℕ) (t : ℝ),
            ∃ tree : DecisionTree F,
              tree.depth = U.card ∧
                (∀ x, tree.eval x = coordinateParity U x) ∧
                firstDerivativeProfile m (coordinateParity U) =
                  Nat.choose U.card m ∧
                derivativeProfileGenerating t (coordinateParity U) =
                  (1 + t) ^ U.card)

end MathlibPlus.Open.Combinatorics
