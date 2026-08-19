import MathlibPlus.Open.Research.R4031Claim51988

namespace MathlibPlus.Open.ResearchFormalization.R4031Claim51981

open scoped BigOperators
open MathlibPlus.Open.Research.R4031Claim51988

noncomputable section

abbrev BooleanLaw (n : ℕ) := Atom n → ℝ

def isProbabilityLaw {n : ℕ} (nu : BooleanLaw n) : Prop :=
  (∀ k, 0 ≤ nu k) ∧
    (∑ k : Atom n, nu k) = 1

noncomputable def lawExpectation {n : ℕ} (nu : BooleanLaw n)
    (f : Atom n → ℝ) : ℝ :=
  ∑ k : Atom n, nu k * f k

noncomputable def lawBarycentre {n : ℕ} (nu : BooleanLaw n) : Table n :=
  fun x => ∑ k : Atom n, nu k * atomValue k x

def historyDetermines {n : ℕ} (k : Atom n) (history : History n) : Prop :=
  ∃ value : Spin, ∀ x, compatible history x → k x = value

noncomputable def cellWeight {n : ℕ} (history : History n) : ℝ :=
  (compatibleCell history).card / (Fintype.card (Cube n) : ℝ)

def QueryTree.nodeHistories {n : ℕ} (history : History n) :
    QueryTree n → List (History n)
  | .leaf _ => [history]
  | .query coordinate negative positive =>
      history ::
        (nodeHistories (observe history coordinate false) negative ++
          nodeHistories (observe history coordinate true) positive)

def QueryTree.queryHistories {n : ℕ} (history : History n) :
    QueryTree n → List (History n)
  | .leaf _ => []
  | .query coordinate negative positive =>
      history ::
        (queryHistories (observe history coordinate false) negative ++
          queryHistories (observe history coordinate true) positive)

def QueryTree.leafHistories {n : ℕ} (history : History n) :
    QueryTree n → List (History n)
  | .leaf _ => [history]
  | .query coordinate negative positive =>
      leafHistories (observe history coordinate false) negative ++
        leafHistories (observe history coordinate true) positive

def QueryTree.restrictAt {n : ℕ} : QueryTree n → History n → QueryTree n
  | .leaf value, _ => .leaf value
  | .query coordinate negative positive, history =>
      match history coordinate with
      | some false => restrictAt negative history
      | some true => restrictAt positive history
      | none => .query coordinate negative positive

noncomputable def completionArea {n : ℕ} (policy : QueryTree n)
    (u : Table n) (history : History n) : ℝ :=
  policyPair (QueryTree.restrictAt policy history) u u history

noncomputable def prefixCharge {n : ℕ} (preTree : QueryTree n)
    (v : Table n) (h : Atom n) : ℝ :=
  ((QueryTree.queryHistories (fun _ => none) preTree).map
    (fun history =>
      cellWeight history *
        (1 - conditionalCovariance (atomValue h) (atomValue h) history +
          conditionalCovariance
            (fun x => atomValue h x - v x)
            (fun x => atomValue h x - v x)
            history))).sum

noncomputable def completionDifference {n : ℕ} (policy preTree : QueryTree n)
    (v : Table n) (h : Atom n) : ℝ :=
  ((QueryTree.leafHistories (fun _ => none) preTree).map
    (fun history =>
      cellWeight history *
        (completionArea policy
            (fun x => atomValue h x - v x) history -
          completionArea policy (atomValue h) history))).sum

noncomputable def determinedCellContribution {n : ℕ}
    (v : Table n) (h k : Atom n) (history : History n) : ℝ :=
  let _ : Decidable (historyDetermines k history) := Classical.propDecidable _
  if historyDetermines k history then
    cellWeight history *
      (conditionalCovariance v v history -
        2 * conditionalCovariance v (atomValue h) history)
  else 0

noncomputable def determinedContribution {n : ℕ} (policy : QueryTree n)
    (v : Table n) (h k : Atom n) : ℝ :=
  ((QueryTree.queryHistories (fun _ => none) policy).map
    (determinedCellContribution v h k)).sum

def qOptimalPrefix {n : ℕ} (k : Atom n) (preTree policy : QueryTree n) : Prop :=
  policy.complete ∧
    preTree.noRepeat ∧
    preTree.determines k ∧
    preTree.prefixOf policy ∧
    preTree.expectedCost = queryCost k

def directionalActive {n : ℕ} (k : Atom n) (u : Table n)
    (h : Atom n) (policy : QueryTree n) : Prop :=
  constrainedActive k u policy ∧
    policyPair policy u (atomValue h) (fun _ => none) =
      constrainedPairing k u h

noncomputable def stoppingScore {n : ℕ} (nu : BooleanLaw n) (h : Atom n) : ℝ :=
  let v := lawBarycentre nu
  constrainedLoss h v - queryCost h +
    lawExpectation nu
      (fun k =>
        2 * constrainedPairing k v h - constrainedLoss k v - queryCost k)

/-- The selected q-optimal-prefix split has the stated completion cancellation,
renewal identity, and determination-lag sign localization. -/
def claim51981 : Prop :=
  ∀ (n : ℕ) (nu : BooleanLaw n) (h : Atom n)
    (prefixH rho : QueryTree n)
    (prefixK : Atom n → QueryTree n)
    (policyK : Atom n → QueryTree n),
    isProbabilityLaw nu →
    qOptimalPrefix h prefixH rho →
    constrainedActive h (lawBarycentre nu) rho →
    (∀ k,
      qOptimalPrefix k (prefixK k) (policyK k) ∧
        directionalActive k (lawBarycentre nu) h (policyK k)) →
      let v := lawBarycentre nu
      (∀ history,
        history ∈ QueryTree.leafHistories (fun _ => none) prefixH →
          completionArea rho
              (fun x => atomValue h x - v x) history =
            completionArea rho v history) ∧
      (∀ k history,
        history ∈ QueryTree.leafHistories
            (fun _ => none) (prefixK k) →
          completionArea (policyK k)
              (fun x => atomValue h x - atomValue k x) history =
            completionArea (policyK k) (atomValue h) history) ∧
      (-stoppingScore nu h =
        queryCost h - policyLoss rho v +
          lawExpectation nu
            (fun k =>
              prefixCharge (prefixK k) v h +
                completionDifference (policyK k) (prefixK k) v h)) ∧
      (∀ k,
        completionDifference (policyK k) (prefixK k) v h =
          determinedContribution (policyK k) v h k) ∧
      (∀ k history,
        history ∈ QueryTree.queryHistories
            (fun _ => none) (policyK k) →
        historyDetermines k history →
        historyDetermines h history →
          determinedCellContribution v h k history =
            cellWeight history * conditionalCovariance v v history ∧
          0 ≤ determinedCellContribution v h k history) ∧
      (∀ k history,
        history ∈ QueryTree.queryHistories
            (fun _ => none) (policyK k) →
        determinedCellContribution v h k history < 0 →
          historyDetermines k history ∧ ¬ historyDetermines h history)

end
end MathlibPlus.Open.ResearchFormalization.R4031Claim51981
