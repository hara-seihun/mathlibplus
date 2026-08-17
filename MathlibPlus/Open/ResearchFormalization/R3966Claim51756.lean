import MathlibPlus.Open.ResearchFormalization.RademacherAndTrees

namespace MathlibPlus.Open.ResearchFormalization.R3966Claim51756

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open scoped BigOperators

/-- The sufficient root-restricted symmetry state. -/
structure SharedState where
  u : ℕ
  p : ℕ
  q : ℕ
  yMinus : Option Bool
  yPlus : Option Bool

def validState (n : ℕ) (s : SharedState) : Prop :=
  s.u + s.p + s.q = n

def trueCount {u : ℕ} (A : Fin u → Bool) : ℕ :=
  (Finset.univ.filter (fun i => A i = true)).card

/-- Uniform expectation of a function of `R ~ Bin(u,1/2)`, implemented by the
uniform cube of unresolved selectors. -/
def binomialExpectation (u : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ A : Fin u → Bool, f (trueCount A)) /
    ((2 ^ u : ℕ) : ℝ)

def stateMatches (n : ℕ) (s : SharedState)
    (w : (Fin n → Bool) × Bool × Bool) : Bool :=
  @decide
    ((∀ i : Fin n, i.val < s.p → w.1 i = false) ∧
      (∀ i : Fin n, s.p ≤ i.val → i.val < s.p + s.q →
        w.1 i = true) ∧
        (match s.yMinus with
        | none => True
        | some y => w.2.1 = y) ∧
          (match s.yPlus with
          | none => True
          | some y => w.2.2 = y))
    (Classical.propDecidable _)

def stateWeight (n : ℕ) (s : SharedState) : ℝ :=
  ∑ w : (Fin n → Bool) × Bool × Bool,
    if stateMatches n s w then (1 : ℝ) else 0

def stateMean (n : ℕ) (s : SharedState) : ℝ :=
  (∑ w : (Fin n → Bool) × Bool × Bool,
      if stateMatches n s w then
        sharedSelectorMu n w.1 w.2.1 w.2.2
      else 0) / stateWeight n s

/-- The actual conditional posterior variance, using the finite independent
uniform-sign world and the canonical representative of a symmetry state. -/
def posteriorVariance (n : ℕ) (s : SharedState) : ℝ :=
  (∑ w : (Fin n → Bool) × Bool × Bool,
      if stateMatches n s w then
        (sharedSelectorMu n w.1 w.2.1 w.2.2 - stateMean n s) ^ 2
      else 0) / stateWeight n s

def currentNumerator (s : SharedState) (r : ℕ)
    (yMinus yPlus : ℝ) : ℝ :=
  ((s.p + r : ℕ) : ℝ) * yMinus +
    ((s.q + s.u - r : ℕ) : ℝ) * yPlus

/-- The four displayed conditional-variance formulas, with the unresolved
selector count averaged through `binomialExpectation`. -/
def statedVariance (n : ℕ) (s : SharedState) : ℝ :=
  match s.yMinus, s.yPlus with
  | none, none =>
      (binomialExpectation s.u (fun r => ((s.p + r : ℕ) : ℝ) ^ 2) +
        binomialExpectation s.u
          (fun r => ((s.q + s.u - r : ℕ) : ℝ) ^ 2)) /
        (n : ℝ) ^ 2
  | some _, none =>
      ((s.u : ℝ) / 4 +
        binomialExpectation s.u
          (fun r => ((s.q + s.u - r : ℕ) : ℝ) ^ 2)) /
        (n : ℝ) ^ 2
  | none, some _ =>
      (binomialExpectation s.u
          (fun r => ((s.p + r : ℕ) : ℝ) ^ 2) +
        (s.u : ℝ) / 4) /
        (n : ℝ) ^ 2
  | some yMinus, some yPlus =>
      (s.u : ℝ) *
          (researchSign yMinus - researchSign yPlus) ^ 2 /
        (4 * (n : ℝ) ^ 2)

/-- Claim 51756: under the root-restricted live-root state semantics, the
actual posterior variance is exactly the four-case formula. -/
def claim51756 : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ s : SharedState, validState n s →
      posteriorVariance n s = statedVariance n s

end

end MathlibPlus.Open.ResearchFormalization.R3966Claim51756
