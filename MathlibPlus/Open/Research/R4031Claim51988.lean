import Mathlib

namespace MathlibPlus.Open.Research.R4031Claim51988

open scoped BigOperators

noncomputable section

abbrev Spin := Bool
abbrev Cube (n : ℕ) := Fin n → Spin
abbrev Atom (n : ℕ) := Cube n → Spin
abbrev Table (n : ℕ) := Cube n → ℝ
abbrev History (n : ℕ) := Fin n → Option Spin

inductive QueryTree (n : ℕ) where
  | leaf (value : Spin) : QueryTree n
  | query (coordinate : Fin n) (negative positive : QueryTree n) : QueryTree n

def QueryTree.evaluate {n : ℕ} : QueryTree n → Cube n → Spin
  | .leaf value, _ => value
  | .query coordinate negative positive, x =>
      if x coordinate then positive.evaluate x else negative.evaluate x

def QueryTree.trace {n : ℕ} : QueryTree n → Cube n → List (Fin n)
  | .leaf _, _ => []
  | .query coordinate negative positive, x =>
      coordinate ::
        if x coordinate then positive.trace x else negative.trace x

def QueryTree.noRepeatFrom {n : ℕ} (seen : Finset (Fin n)) : QueryTree n → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ seen ∧
        noRepeatFrom (insert coordinate seen) negative ∧
        noRepeatFrom (insert coordinate seen) positive

def QueryTree.noRepeat {n : ℕ} (tree : QueryTree n) : Prop :=
  tree.noRepeatFrom ∅

def QueryTree.complete {n : ℕ} (tree : QueryTree n) : Prop :=
  tree.noRepeat ∧ ∀ x : Cube n, (tree.trace x).length = n

def QueryTree.determines {n : ℕ} (tree : QueryTree n) (k : Atom n) : Prop :=
  ∀ x, tree.evaluate x = k x

def QueryTree.prefixOf {n : ℕ} (preTree full : QueryTree n) : Prop :=
  ∀ x, List.IsPrefix (preTree.trace x) (full.trace x)

def QueryTree.root {n : ℕ} : QueryTree n → Option (Fin n)
  | .leaf _ => none
  | .query coordinate _ _ => some coordinate

def QueryTree.expectedCost {n : ℕ} : QueryTree n → ℝ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + (negative.expectedCost + positive.expectedCost) / 2

def spinValue (s : Spin) : ℝ := if s then 1 else -1

def atomValue {n : ℕ} (k : Atom n) : Table n := fun x => spinValue (k x)

def observe {n : ℕ} (history : History n) (coordinate : Fin n) (value : Spin) : History n :=
  Function.update history coordinate (some value)

def compatible {n : ℕ} (history : History n) (x : Cube n) : Prop :=
  ∀ coordinate value, history coordinate = some value → x coordinate = value

noncomputable def compatibleCell {n : ℕ} (history : History n) : Finset (Cube n) := by
  classical
  exact Finset.univ.filter (fun x => compatible history x)

noncomputable def conditionalMean {n : ℕ} (u : Table n) (history : History n) : ℝ := by
  classical
  let cell := compatibleCell history
  exact if cell.Nonempty then
    (cell.sum u) / (cell.card : ℝ)
  else 0

noncomputable def conditionalCovariance {n : ℕ}
    (u w : Table n) (history : History n) : ℝ := by
  classical
  let cell := compatibleCell history
  let mu := conditionalMean u history
  let mw := conditionalMean w history
  exact if cell.Nonempty then
    (cell.sum (fun x => (u x - mu) * (w x - mw))) / (cell.card : ℝ)
  else 0

noncomputable def policyPair {n : ℕ} : QueryTree n → Table n → Table n → History n → ℝ
  | .leaf _, _, _, _ => 0
  | .query coordinate negative positive, u, w, history =>
      conditionalCovariance u w history +
        (policyPair negative u w (observe history coordinate false) +
          policyPair positive u w (observe history coordinate true)) / 2

noncomputable def policyLoss {n : ℕ} (policy : QueryTree n) (u : Table n) : ℝ :=
  policyPair policy u u (fun _ => none)

noncomputable def queryCost {n : ℕ} (k : Atom n) : ℝ :=
  sInf {r : ℝ |
    ∃ preTree : QueryTree n,
      preTree.noRepeat ∧ preTree.determines k ∧ r = preTree.expectedCost}

def qPolicy {n : ℕ} (k : Atom n) (policy : QueryTree n) : Prop :=
  policy.complete ∧
    ∃ preTree : QueryTree n,
      preTree.noRepeat ∧
        preTree.determines k ∧
        preTree.prefixOf policy ∧
        preTree.expectedCost = queryCost k

noncomputable def constrainedLoss {n : ℕ} (k : Atom n) (u : Table n) : ℝ :=
  sInf {r : ℝ | ∃ policy : QueryTree n, qPolicy k policy ∧ r = policyLoss policy u}

def constrainedActive {n : ℕ} (k : Atom n) (u : Table n)
    (policy : QueryTree n) : Prop :=
  qPolicy k policy ∧ policyLoss policy u = constrainedLoss k u

noncomputable def unrestrictedLoss {n : ℕ} (u : Table n) : ℝ :=
  sInf {r : ℝ | ∃ policy : QueryTree n, policy.complete ∧ r = policyLoss policy u}

def unrestrictedActive {n : ℕ} (u : Table n) (policy : QueryTree n) : Prop :=
  policy.complete ∧ policyLoss policy u = unrestrictedLoss u

noncomputable def constrainedPairing {n : ℕ}
    (k : Atom n) (u : Table n) (h : Atom n) : ℝ :=
  sInf {r : ℝ |
    ∃ policy : QueryTree n,
      constrainedActive k u policy ∧
        r = policyPair policy u (atomValue h) (fun _ => none)}

noncomputable def unrestrictedPairing {n : ℕ}
    (u : Table n) (h : Atom n) : ℝ :=
  sInf {r : ℝ |
    ∃ policy : QueryTree n,
      unrestrictedActive u policy ∧
        r = policyPair policy u (atomValue h) (fun _ => none)}

noncomputable def cValue {n : ℕ} (u : Table n) (h k : Atom n) : ℝ :=
  queryCost k + constrainedLoss k u - 2 * constrainedPairing k u h

noncomputable def rootCharge {n : ℕ} (u : Table n) (h : Atom n) : ℝ :=
  1 +
      (conditionalCovariance u u (fun _ => none)) -
      2 * conditionalCovariance u (atomValue h) (fun _ => none)

def isConstant {n : ℕ} (k : Atom n) : Prop :=
  ∃ value : Spin, ∀ x, k x = value

def fixTable {n : ℕ} (u : Table n) (coordinate : Fin n) (value : Spin) : Table n :=
  fun x => u (Function.update x coordinate value)

def fixAtom {n : ℕ} (k : Atom n) (coordinate : Fin n) (value : Spin) : Atom n :=
  fun x => k (Function.update x coordinate value)

noncomputable def bellmanExpansion {n : ℕ} : QueryTree n → Table n → Atom n → ℝ
  | .leaf _, u, h => unrestrictedLoss u - 2 * unrestrictedPairing u h
  | .query coordinate negative positive, u, h =>
      rootCharge u h +
        (bellmanExpansion negative (fixTable u coordinate false) (fixAtom h coordinate false) +
          bellmanExpansion positive (fixTable u coordinate true) (fixAtom h coordinate true)) / 2

def selectedQOptimalRoot {n : ℕ}
    (u : Table n) (h k : Atom n) (preTree : QueryTree n)
    (policy : QueryTree n) (coordinate : Fin n) : Prop :=
  preTree.noRepeat ∧
    preTree.determines k ∧
    preTree.prefixOf policy ∧
    preTree.expectedCost = queryCost k ∧
    preTree.root = some coordinate ∧
    constrainedActive k u policy ∧
    policyPair policy u (atomValue h) (fun _ => none) = constrainedPairing k u h

def claim51988 : Prop :=
  (∀ (n : ℕ) (u : Table n) (h k : Atom n)
      (preTree policy : QueryTree n) (coordinate : Fin n),
    ¬ isConstant k →
      selectedQOptimalRoot u h k preTree policy coordinate →
      cValue u h k =
        rootCharge u h +
          (cValue (fixTable u coordinate false)
              (fixAtom h coordinate false) (fixAtom k coordinate false) +
            cValue (fixTable u coordinate true)
              (fixAtom h coordinate true) (fixAtom k coordinate true)) / 2) ∧
  (∀ (n : ℕ) (u : Table n) (h : Atom n),
    rootCharge u h =
        1 -
          (conditionalCovariance (atomValue h) (atomValue h) (fun _ => none)) +
          conditionalCovariance
            (fun x => u x - atomValue h x)
            (fun x => u x - atomValue h x)
            (fun _ => none) ∧
      0 ≤ rootCharge u h) ∧
  (∀ (n : ℕ) (u : Table n) (h k : Atom n),
    isConstant k → cValue u h k = unrestrictedLoss u - 2 * unrestrictedPairing u h) ∧
  (∀ (n : ℕ) (u : Table n) (h k : Atom n)
      (preTree policy : QueryTree n) (coordinate : Fin n),
    ¬ isConstant k →
      selectedQOptimalRoot u h k preTree policy coordinate →
      cValue u h k = bellmanExpansion preTree u h)

end
end MathlibPlus.Open.Research.R4031Claim51988
