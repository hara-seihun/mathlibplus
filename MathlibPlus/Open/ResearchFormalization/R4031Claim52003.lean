import MathlibPlus.Open.Research.R4031Claim51988

namespace MathlibPlus.Open.ResearchFormalization.R4031Claim52003

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

noncomputable def diracLaw {n : ℕ} (h : Atom n) : BooleanLaw n :=
  fun k => if k = h then 1 else 0

noncomputable def radialLaw {n : ℕ} (h : Atom n) (nu : BooleanLaw n)
    (beta : ℝ) : BooleanLaw n :=
  fun k => (1 - beta) * diracLaw h k + beta * nu k

noncomputable def radialPoint {n : ℕ} (h : Atom n) (nu : BooleanLaw n)
    (beta : ℝ) : Table n :=
  atomValue h + beta • (lawBarycentre nu - atomValue h)

noncomputable def lawAverageLoss {n : ℕ} (nu : BooleanLaw n)
    (policies : Atom n → QueryTree n) (u : Table n) : ℝ :=
  ∑ k : Atom n, nu k * policyLoss (policies k) u

noncomputable def lawAverageQueryCost {n : ℕ} (nu : BooleanLaw n) : ℝ :=
  lawExpectation nu queryCost

noncomputable def radialScore {n : ℕ} (law : BooleanLaw n)
    (h : Atom n) : ℝ :=
  let u := lawBarycentre law
  constrainedLoss h u - queryCost h +
    lawExpectation law
      (fun k =>
        2 * constrainedPairing k u h - constrainedLoss k u - queryCost k)

def directionalActive {n : ℕ} (k : Atom n) (u : Table n)
    (h : Atom n) (policy : QueryTree n) : Prop :=
  constrainedActive k u policy ∧
    policyPair policy u (atomValue h) (fun _ => none) =
      constrainedPairing k u h

def activePolicyTuple {n : ℕ} (nu : BooleanLaw n) (h : Atom n)
    (beta : ℝ) (Qh : QueryTree n) (Q : Atom n → QueryTree n) : Prop :=
  0 ≤ beta ∧ beta ≤ 1 ∧
    directionalActive h (radialPoint h nu beta) h Qh ∧
    ∀ k, directionalActive k (radialPoint h nu beta) h (Q k)

def hActive {n : ℕ} (u : Table n) (h : Atom n)
    (rho : QueryTree n) : Prop :=
  unrestrictedActive u rho ∧
    policyPair rho u (atomValue h) (fun _ => none) =
      unrestrictedPairing u h

noncomputable def lawRoof {n : ℕ} (nu : BooleanLaw n) : ℝ :=
  let u := lawBarycentre nu
  lawExpectation nu (fun k => constrainedLoss k u - queryCost k)

noncomputable def policyBranchRoof {n : ℕ} (nu : BooleanLaw n)
    (h : Atom n) (beta : ℝ) (Qh : QueryTree n)
    (Q : Atom n → QueryTree n) : ℝ :=
  let u := radialPoint h nu beta
  (1 - beta) * (policyLoss Qh u - queryCost h) +
    beta * (lawAverageLoss nu Q u - lawAverageQueryCost nu)

noncomputable def policySidecar {n : ℕ} (nu : BooleanLaw n)
    (h : Atom n) (beta : ℝ) (Qh : QueryTree n)
    (Q : Atom n → QueryTree n) : ℝ :=
  let v := lawBarycentre nu
  let d := v - atomValue h
  policyLoss Qh (atomValue h) - queryCost h +
    beta *
      (2 * policyPair Qh (atomValue h) d (fun _ => none) +
        lawAverageLoss nu Q (atomValue h) - lawAverageQueryCost nu) +
    beta ^ 2 *
      (policyLoss Qh d - lawAverageLoss nu Q d)

noncomputable def endpointPolicyRegret {n : ℕ} (nu : BooleanLaw n)
    (Q : Atom n → QueryTree n) : ℝ :=
  let v := lawBarycentre nu
  lawExpectation nu (fun k => policyLoss (Q k) v - constrainedLoss k v)

noncomputable def policyExchangeScore {n : ℕ} (nu : BooleanLaw n)
    (h : Atom n) : ℝ :=
  radialScore nu h

noncomputable def reserveExcess {n : ℕ} (nu : BooleanLaw n)
    (h : Atom n) (beta : ℝ) (Q : Atom n → QueryTree n)
    (rho : QueryTree n) : ℝ :=
  let v := lawBarycentre nu
  beta *
      (lawAverageLoss nu Q (v - atomValue h) -
        policyLoss rho (v - atomValue h)) -
    (queryCost h - policyLoss rho (atomValue h))

noncomputable def reserveInequalityFalse : Prop :=
  ∃ (n : ℕ) (nu : BooleanLaw n) (h : Atom n) (beta : ℝ)
    (Qh rho : QueryTree n) (Q : Atom n → QueryTree n),
    isProbabilityLaw nu ∧
      activePolicyTuple nu h beta Qh Q ∧
      hActive (lawBarycentre nu) h rho ∧
      reserveExcess nu h beta Q rho > 0

/-- The active policy branch, endpoint regret, true law roof defect, and exact
policy-exchange bound are tied to the concrete finite Boolean policy carrier;
the final conjunct records the false reserve inequality using an actual
h-active policy rather than a stronger directional constrained-active premise. -/
def claim52003 : Prop :=
  (∀ (n : ℕ) (nu : BooleanLaw n) (h : Atom n) (beta : ℝ)
    (Qh rho : QueryTree n) (Q : Atom n → QueryTree n),
    isProbabilityLaw nu →
    activePolicyTuple nu h beta Qh Q →
    hActive (lawBarycentre nu) h rho →
      let v := lawBarycentre nu
      let d := v - atomValue h
      policyBranchRoof nu h beta Qh Q -
          beta ^ 2 * policyBranchRoof nu h 1 Qh Q =
        (1 - beta) * policySidecar nu h beta Qh Q ∧
      0 ≤ endpointPolicyRegret nu Q ∧
      lawRoof (radialLaw h nu beta) - beta ^ 2 * lawRoof nu =
        (1 - beta) * policySidecar nu h beta Qh Q +
          beta ^ 2 * endpointPolicyRegret nu Q ∧
      lawRoof (radialLaw h nu beta) - beta ^ 2 * lawRoof nu ≤
        beta * (1 - beta) * policyExchangeScore nu h +
          (1 - beta) ^ 2 *
            (policyLoss rho (atomValue h) - queryCost h +
              beta *
                (lawAverageLoss nu Q (v - atomValue h) -
                  policyLoss rho (v - atomValue h)))) ∧
  reserveInequalityFalse

end
end MathlibPlus.Open.ResearchFormalization.R4031Claim52003
