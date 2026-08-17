import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDepthOneClaim61063

noncomputable section
open Classical

abbrev Sign := Bool

def signValue : Sign → ℝ
  | false => -1
  | true => 1

/-- A sign-valued deterministic tree of depth at most one. -/
inductive SignStump (Q : Type*) where
  | constant : Sign → SignStump Q
  | query : Q → Sign → Sign → SignStump Q

namespace SignStump

def eval {Q : Type*} : SignStump Q → (Q → Sign) → Sign
  | .constant value, _ => value
  | .query q negative positive, x =>
      if x q then positive else negative

def intercept {Q : Type*} : SignStump Q → ℝ
  | .constant value => signValue value
  | .query _ negative positive =>
      (signValue negative + signValue positive) / 2

def slope {Q : Type*} [DecidableEq Q] : SignStump Q → Q → ℝ
  | .constant _, _ => 0
  | .query q negative positive, i =>
      if q = i then
        (signValue positive - signValue negative) / 2
      else 0
end SignStump

abbrev Outcome (Q : Type*) := Q → Sign
abbrev History (Q : Type*) := Q → Option Sign
abbrev Policy (Q : Type*) := History Q → Option Q

def initialHistory {Q : Type*} : History Q := fun _ => none

def observe {Q : Type*} (h : History Q) (x : Outcome Q) (q : Q) : History Q :=
  Function.update h q (some (x q))

def compatible {Q : Type*} (h : History Q) (x : Outcome Q) : Prop :=
  ∀ q, ∀ s, h q = some s → x q = s

noncomputable def compatibleOutcomes {Q : Type*} [Fintype Q] [DecidableEq Q]
    (h : History Q) : Finset (Outcome Q) :=
  Finset.univ.filter (fun x => compatible h x)

def averageOn {Q : Type*} (f : Outcome Q → ℝ)
    (s : Finset (Outcome Q)) : ℝ :=
  if s.Nonempty then
    (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x
  else 0

def varianceOn {Q : Type*} (f : Outcome Q → ℝ)
    (s : Finset (Outcome Q)) : ℝ :=
  averageOn (fun x => (f x - averageOn f s) ^ 2) s

def posteriorVariance {Q : Type*} [Fintype Q] [DecidableEq Q]
    (f : Outcome Q → ℝ) (h : History Q) : ℝ :=
  varianceOn f (compatibleOutcomes h)

def historyAt {Q : Type*} (π : Policy Q) (x : Outcome Q) : ℕ → History Q
  | 0 => initialHistory
  | n + 1 =>
      let h := historyAt π x n
      match π h with
      | none => h
      | some q => observe h x q

def legalPolicy {Q : Type*} [DecidableEq Q]
    (π : Policy Q) : Prop :=
  ∀ h q, π h = some q → h q = none

def targetDetermined {Q : Type*} [Fintype Q] [DecidableEq Q]
    (f : Outcome Q → ℝ) (π : Policy Q) : Prop :=
  ∀ x, ∃ n, ∀ y,
    compatible (historyAt π x n) y → f y = f x

def uniformExpectation {Q : Type*} [Fintype Q]
    (f : Outcome Q → ℝ) : ℝ :=
  (Fintype.card (Outcome Q) : ℝ)⁻¹ * ∑ x : Outcome Q, f x

def policyArea {Q : Type*} [Fintype Q] [DecidableEq Q]
    (f : Outcome Q → ℝ) (π : Policy Q) : ℝ :=
  ∑' n : ℕ,
    uniformExpectation (fun x => posteriorVariance f (historyAt π x n))

noncomputable def randomizedPolicyArea {Q : Type*} [Fintype Q] [DecidableEq Q]
    (f : Outcome Q → ℝ) (p : Policy Q → ℝ) : ℝ :=
  ∑ π : Policy Q, p π * policyArea f π

def validRandomizedPolicy {Q : Type*} [Fintype Q] [DecidableEq Q]
    (f : Outcome Q → ℝ) (p : Policy Q → ℝ) : Prop :=
  (∀ π, 0 ≤ p π) ∧
    (∑ π : Policy Q, p π = 1) ∧
    (∀ π, p π ≠ 0 → legalPolicy π ∧ targetDetermined f π)

def mixtureMean {Q : Type*} (m : ℕ) (weights : Fin m → ℝ)
    (trees : Fin m → SignStump Q) (x : Outcome Q) : ℝ :=
  ∑ t : Fin m, weights t * signValue ((trees t).eval x)

def mixtureIntercept {Q : Type*} (m : ℕ) (weights : Fin m → ℝ)
    (trees : Fin m → SignStump Q) : ℝ :=
  ∑ t : Fin m, weights t * (trees t).intercept

def aggregateCoefficient {Q : Type*} [DecidableEq Q]
    (m : ℕ) (weights : Fin m → ℝ) (trees : Fin m → SignStump Q)
    (q : Q) : ℝ :=
  ∑ t : Fin m, weights t * (trees t).slope q

def validMixture (m : ℕ) (weights : Fin m → ℝ) : Prop :=
  (∀ t, 0 ≤ weights t) ∧ ∑ t : Fin m, weights t = 1

def affineExpansion {Q : Type*} [Fintype Q] [DecidableEq Q]
    (m : ℕ) (weights : Fin m → ℝ) (trees : Fin m → SignStump Q) : Prop :=
  ∀ x : Outcome Q,
    mixtureMean m weights trees x =
      mixtureIntercept m weights trees +
        ∑ q : Q,
          aggregateCoefficient m weights trees q * signValue (x q)

/-- A ranking contains exactly the nonzero aggregate coordinates, in decreasing
absolute coefficient order. -/
structure RankedCoordinates {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a : Q → ℝ) where
  n : ℕ
  coord : Fin n → Q
  nonzero : ∀ i, a (coord i) ≠ 0
  complete : ∀ q, a q ≠ 0 → ∃ i, coord i = q
  injective : Function.Injective coord
  ordered : ∀ i j, i.1 < j.1 → |a (coord j)| ≤ |a (coord i)|

def rankedMagnitude {Q : Type*} [Fintype Q] [DecidableEq Q]
    {a : Q → ℝ} (r : RankedCoordinates a) (i : Fin r.n) : ℝ :=
  |a (r.coord i)|

def unseenRanks {Q : Type*} [Fintype Q] [DecidableEq Q]
    {a : Q → ℝ} (r : RankedCoordinates a) (h : History Q) : Finset (Fin r.n) :=
  Finset.univ.filter (fun i => h (r.coord i) = none)

noncomputable def rankedPolicy {Q : Type*} [Fintype Q] [DecidableEq Q]
    {a : Q → ℝ} (r : RankedCoordinates a) : Policy Q :=
  fun h =>
    if hs : (unseenRanks r h).Nonempty then
      some (r.coord ((unseenRanks r h).min' hs))
    else none

def rankedAreaValue {Q : Type*} [Fintype Q] [DecidableEq Q]
    {a : Q → ℝ} (r : RankedCoordinates a) : ℝ :=
  ∑ i : Fin r.n,
    (i.1 + 1 : ℝ) * (rankedMagnitude r i) ^ 2

/-- Claim 61063: for every finite mixture of sign-valued depth-one trees on
independent uniform sign coordinates, the aggregate-coefficient ranking is a
legal determining policy with the exact ranked-square area, and no legal
transcript-adaptive or independently randomized policy has smaller area. -/
def claim61063 : Prop :=
  ∀ {Q : Type*} [Fintype Q] [DecidableEq Q]
    (m : ℕ) (weights : Fin m → ℝ) (trees : Fin m → SignStump Q),
    validMixture m weights →
      let μ := mixtureMean m weights trees
      let a := aggregateCoefficient m weights trees
      ∃ r : RankedCoordinates a,
        affineExpansion m weights trees ∧
          legalPolicy (rankedPolicy r) ∧
          targetDetermined μ (rankedPolicy r) ∧
          policyArea μ (rankedPolicy r) = rankedAreaValue r ∧
          rankedAreaValue r ≤
            (∑ i : Fin r.n, rankedMagnitude r i) ^ 2 ∧
          (∑ i : Fin r.n, rankedMagnitude r i) ^ 2 ≤ 1 ∧
          (∀ π : Policy Q,
            legalPolicy π → targetDetermined μ π →
              rankedAreaValue r ≤ policyArea μ π) ∧
          (∀ p : Policy Q → ℝ,
            validRandomizedPolicy μ p →
              rankedAreaValue r ≤ randomizedPolicyArea μ p)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDepthOneClaim61063
