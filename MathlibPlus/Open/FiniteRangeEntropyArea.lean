import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.FiniteRangeEntropyArea

universe u v

open Classical

/-- A finite law represented by its real masses and an explicit finite support. -/
def IsFiniteLaw {α : Type*} (mass : α → ℝ) (support : Finset α) : Prop :=
  (∀ a, 0 ≤ mass a) ∧
    (support.sum (fun a => mass a) = 1) ∧
      (∀ a, a ∉ support → mass a = 0)

/-- A finite probability model on a finite sample space. -/
def IsFiniteProbability {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ mass ω) ∧ (∑ ω, mass ω = 1)

/-- Expectation of a real observable under a finitely supported law. -/
def finiteExpectation {α : Type*} (mass : α → ℝ) (support : Finset α)
    (observable : α → ℝ) : ℝ :=
  support.sum (fun a => mass a * observable a)

/-- Base-two Shannon entropy of a finitely supported real law. -/
def entropyTwo {α : Type*} (mass : α → ℝ) (support : Finset α) : ℝ :=
  support.sum (fun a => -mass a * Real.logb 2 (mass a))

/-- The law of a random variable on a finite sample space. -/
def IsLawOf {Ω α : Type*} [Fintype Ω] (sampleMass : Ω → ℝ)
    (randomVariable : Ω → α) (mass : α → ℝ) : Prop :=
  ∀ a, mass a = ∑ ω, if randomVariable ω = a then sampleMass ω else 0

/-- A support-wise range condition for a law on real-valued functions. -/
def IsRangeBounded {α : Type*} (a b : ℝ) (massSupport : Finset (α → ℝ)) : Prop :=
  ∀ f ∈ massSupport, ∀ x, a ≤ f x ∧ f x ≤ b

/-- One query-answer symbol and a preceding adaptive history. -/
def QueryAnswer (X : Type*) := X × ℝ

def QueryHistory (X : Type*) (t : ℕ) := Fin t → QueryAnswer X

/-- The query-answer history preceding round `t`. -/
def priorHistory {X Ω : Type*} (T : ℕ) (F : Ω → X → ℝ)
    (Q : Fin T → Ω → X) (t : Fin T) (ω : Ω) : QueryHistory X t.val :=
  fun i =>
    let s : Fin T := ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩
    (Q s ω, F ω (Q s ω))

/-- Probability mass of a fiber of a finite random variable. -/
def fiberMass {Ω β : Type*} [Fintype Ω] (sampleMass : Ω → ℝ)
    (observable : Ω → β) (value : β) : ℝ :=
  ∑ ω, if observable ω = value then sampleMass ω else 0

/-- Conditional variance on a finite fiber, with zero-probability fibers harmlessly
assigned the field-theoretic value obtained by division by zero. -/
def conditionalVariance {Ω β : Type*} [Fintype Ω] (sampleMass : Ω → ℝ)
    (observable : Ω → ℝ) (conditioning : Ω → β) (ω : Ω) : ℝ :=
  let denominator := fiberMass sampleMass conditioning (conditioning ω)
  let conditionalMean :=
    (∑ ω', if conditioning ω' = conditioning ω then sampleMass ω' * observable ω' else 0) /
      denominator
  (∑ ω',
      if conditioning ω' = conditioning ω then
        sampleMass ω' * (observable ω' - conditionalMean) ^ 2
      else 0) / denominator

/-- The displayed adaptive conditional-variance sum. -/
def adaptiveVarianceRound {X Ω : Type*} [Fintype Ω] (T : ℕ)
    (sampleMass : Ω → ℝ) (F : Ω → X → ℝ) (Q : Fin T → Ω → X) (t : Fin T) : ℝ :=
  ∑ ω,
    sampleMass ω *
      conditionalVariance sampleMass
        (fun ω' => F ω' (Q t ω'))
        (fun ω' => (priorHistory T F Q t ω', Q t ω')) ω

def adaptiveVarianceSum {X Ω : Type*} [Fintype Ω] (T : ℕ)
    (sampleMass : Ω → ℝ) (F : Ω → X → ℝ) (Q : Fin T → Ω → X) : ℝ :=
  ∑ t, adaptiveVarianceRound T sampleMass F Q t

/-- Discrete conditional independence of the round query and the random function,
given the preceding query-answer history. -/
def IsNonanticipating {X Ω : Type*} [Fintype Ω] (T : ℕ)
    (sampleMass : Ω → ℝ) (F : Ω → X → ℝ) (Q : Fin T → Ω → X) : Prop :=
  ∀ (t : Fin T) (q : X) (f : X → ℝ) (h : QueryHistory X t.val),
    fiberMass sampleMass
        (fun ω => (Q t ω, F ω, priorHistory T F Q t ω)) (q, f, h) *
        fiberMass sampleMass (fun ω => priorHistory T F Q t ω) h =
      fiberMass sampleMass (fun ω => (Q t ω, priorHistory T F Q t ω)) (q, h) *
        fiberMass sampleMass (fun ω => (F ω, priorHistory T F Q t ω)) (f, h)

/-- A binary decision tree whose leaves are real labels. -/
inductive DecisionTree (n : ℕ) where
  | leaf (value : ℝ)
  | node (query : Fin n) (zeroBranch oneBranch : DecisionTree n)

/-- Evaluation of a decision tree on a Boolean input. -/
def DecisionTree.eval {n : ℕ} : DecisionTree n → (Fin n → Bool) → ℝ
  | .leaf value, _ => value
  | .node query zeroBranch oneBranch, x =>
      if x query then oneBranch.eval x else zeroBranch.eval x

/-- Depth of a decision tree. -/
def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _ => 0
  | .node _ zeroBranch oneBranch =>
      Nat.succ (max zeroBranch.depth oneBranch.depth)

/-- The predicate that a tree computes a function. -/
def Computes {n : ℕ} (tree : DecisionTree n)
    (f : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x, tree.eval x = f x

/-- Deterministic decision-tree depth, defined as the infimum of realizing depths. -/
def decisionTreeDepth {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℕ :=
  sInf {d : ℕ | ∃ tree : DecisionTree n, tree.depth = d ∧ Computes tree f}

/-- The finite-prior complexity `A_R`. -/
def finitePriorComplexity (n : ℕ) (R : ℝ)
    (mass : ((Fin n → Bool) → ℝ) → ℝ)
    (support : Finset ((Fin n → Bool) → ℝ)) : ℝ :=
  finiteExpectation mass support (fun f => (decisionTreeDepth f : ℝ)) +
    (R ^ 2 / 4) * entropyTwo mass support

/-- A finite mixture law with component laws indexed by a finite label. -/
def IsFiniteMixture {J α : Type*} [Fintype J]
    (labelMass : J → ℝ)
    (mixtureMass : α → ℝ)
    (mixtureSupport : Finset α)
    (componentMass : J → α → ℝ)
    (componentSupport : J → Finset α) : Prop :=
  IsFiniteProbability labelMass ∧
    (∀ j, IsFiniteLaw (componentMass j) (componentSupport j)) ∧
      IsFiniteLaw mixtureMass mixtureSupport ∧
        (∀ a, mixtureMass a = ∑ j, labelMass j * componentMass j a)

/-- The finite-range adaptive variance-entropy theorem. -/
def finiteRangeEntropyAreaVarianceBound : Prop :=
  ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
    (T : ℕ) (a b : ℝ)
    (sampleMass : Ω → ℝ)
    (F : Ω → X → ℝ)
    (Q : Fin T → Ω → X)
    (lawMass : (X → ℝ) → ℝ)
    (lawSupport : Finset (X → ℝ)),
    a ≤ b →
    IsFiniteProbability sampleMass →
    IsFiniteLaw lawMass lawSupport →
    IsLawOf sampleMass F lawMass →
    IsRangeBounded a b lawSupport →
    IsNonanticipating T sampleMass F Q →
    adaptiveVarianceSum T sampleMass F Q ≤
        ((b - a) ^ 2 / 4) * entropyTwo lawMass lawSupport

/-- The definition of `A_R` controls the displayed adaptive variance sum on the Boolean cube. -/
def finitePriorComplexityAdaptiveControl : Prop :=
  ∀ {Ω : Type*} [Fintype Ω]
    (n T : ℕ) (a b : ℝ)
    (sampleMass : Ω → ℝ)
    (F : Ω → (Fin n → Bool) → ℝ)
    (Q : Fin T → Ω → (Fin n → Bool))
    (lawMass : ((Fin n → Bool) → ℝ) → ℝ)
    (lawSupport : Finset ((Fin n → Bool) → ℝ)),
    a ≤ b →
    IsFiniteProbability sampleMass →
    IsFiniteLaw lawMass lawSupport →
    IsLawOf sampleMass F lawMass →
    IsRangeBounded a b lawSupport →
    IsNonanticipating T sampleMass F Q →
    adaptiveVarianceSum T sampleMass F Q ≤
      finitePriorComplexity n (b - a) lawMass lawSupport

/-- The complexity and mixture inequality for the special Boolean-cube prior. -/
def finitePriorComplexityMixtureBound : Prop :=
  ∀ {J : Type*} [Fintype J] (n : ℕ) (a b : ℝ)
    (labelMass : J → ℝ)
    (mixtureMass : ((Fin n → Bool) → ℝ) → ℝ)
    (mixtureSupport : Finset ((Fin n → Bool) → ℝ))
    (componentMass : J → ((Fin n → Bool) → ℝ) → ℝ)
    (componentSupport : J → Finset ((Fin n → Bool) → ℝ)),
    a ≤ b →
    IsFiniteMixture labelMass mixtureMass mixtureSupport componentMass componentSupport →
    finitePriorComplexity n (b - a) mixtureMass mixtureSupport ≤
      (∑ j, labelMass j *
        finitePriorComplexity n (b - a) (componentMass j) (componentSupport j)) +
        ((b - a) ^ 2 / 4) * entropyTwo labelMass Finset.univ

/-- The point-mass consequence and its logarithmic label overhead. -/
def finiteRangeEntropyAreaPointMassConsequence : Prop :=
  ∀ {J : Type*} [Fintype J]
    (n M k : ℕ) (a b : ℝ)
    (labelMass : J → ℝ)
    (mixtureMass : ((Fin n → Bool) → ℝ) → ℝ)
    (mixtureSupport : Finset ((Fin n → Bool) → ℝ))
    (g : J → (Fin n → Bool) → ℝ),
    0 < M →
    Fintype.card J = M →
    a ≤ b →
    IsFiniteProbability labelMass →
    IsFiniteLaw mixtureMass mixtureSupport →
    (∀ f, mixtureMass f = ∑ j, labelMass j * (if f = g j then 1 else 0)) →
    (∀ j x, a ≤ g j x ∧ g j x ≤ b) →
    (∀ j, decisionTreeDepth (g j) ≤ k) →
    finitePriorComplexity n (b - a) mixtureMass mixtureSupport ≤
        (k : ℝ) + ((b - a) ^ 2 / 4) * entropyTwo labelMass Finset.univ ∧
      (k : ℝ) + ((b - a) ^ 2 / 4) * entropyTwo labelMass Finset.univ ≤
        (k : ℝ) + ((b - a) ^ 2 / 4) * Real.logb 2 (M : ℝ)

/-- Uniformly mixing the two constant functions realizes equality in the variance-entropy
bound after one query. -/
def finiteRangeEntropyAreaSharpness : Prop :=
  ∀ (n : ℕ) (a b : ℝ), a < b →
    let f₀ : (Fin n → Bool) → ℝ := fun _ => a
    let f₁ : (Fin n → Bool) → ℝ := fun _ => b
    let sampleMass : Bool → ℝ := fun _ => 1 / 2
    let F : Bool → (Fin n → Bool) → ℝ := fun j => if j then f₁ else f₀
    let Q : Fin 1 → Bool → (Fin n → Bool) := fun _ _ _ => false
    let lawMass : ((Fin n → Bool) → ℝ) → ℝ :=
      fun f => if f = f₀ then 1 / 2 else if f = f₁ then 1 / 2 else 0
    let lawSupport : Finset ((Fin n → Bool) → ℝ) := {f₀, f₁}
    IsFiniteProbability sampleMass ∧
      IsFiniteLaw lawMass lawSupport ∧
      IsLawOf sampleMass F lawMass ∧
      IsRangeBounded a b lawSupport ∧
      IsNonanticipating 1 sampleMass F Q ∧
      adaptiveVarianceSum 1 sampleMass F Q =
        ((b - a) ^ 2 / 4) * entropyTwo lawMass lawSupport

/-- All clauses of the admitted finite-range entropy-area theorem. -/
def finiteRangeEntropyAreaTheorem : Prop :=
  finiteRangeEntropyAreaVarianceBound.{u, v} ∧
    finitePriorComplexityAdaptiveControl.{u} ∧
      finitePriorComplexityMixtureBound.{u} ∧
        finiteRangeEntropyAreaPointMassConsequence.{u} ∧
          finiteRangeEntropyAreaSharpness

end MathlibPlus.Open.FiniteRangeEntropyArea
