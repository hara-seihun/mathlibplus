import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Probability.ResearchBatch

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool

/-- A finite deterministic coordinate-query policy.  A leaf means that the
policy stops; validity below prevents a coordinate from being queried twice on
one branch. -/
inductive QueryTree (n : ℕ) where
  | leaf : QueryTree n
  | node (i : Fin n) (left right : QueryTree n) : QueryTree n

/-- Validity relative to the coordinates already queried on the current path. -/
def validFrom {n : ℕ} (used : Finset (Fin n)) : QueryTree n → Prop
  | .leaf => True
  | .node i left right =>
      i ∉ used ∧ validFrom (insert i used) left ∧ validFrom (insert i used) right

def valid {n : ℕ} (t : QueryTree n) : Prop := validFrom ∅ t

/-- The two cells reached after querying coordinate `i`. -/
def childCell {n : ℕ} (C : Finset (Cube n)) (i : Fin n) (b : Bool) : Finset (Cube n) := by
  classical
  exact C.filter (fun x => x i = b)

def constantOn {n : ℕ} (g : Cube n → ℝ) (C : Finset (Cube n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, g x = g y

/-- Every leaf is required to have already determined the target. -/
def completeFrom {n : ℕ} (g : Cube n → ℝ) : QueryTree n → Finset (Cube n) → Prop
  | .leaf, C => constantOn g C
  | .node i left right, C =>
      completeFrom g left (childCell C i false) ∧
        completeFrom g right (childCell C i true)

def complete {n : ℕ} (g : Cube n → ℝ) (t : QueryTree n) : Prop :=
  completeFrom g t (Finset.univ : Finset (Cube n))

def meanOn {n : ℕ} (g : Cube n → ℝ) (C : Finset (Cube n)) : ℝ :=
  (∑ x ∈ C, g x) / (C.card : ℝ)

def varianceOn {n : ℕ} (g : Cube n → ℝ) (C : Finset (Cube n)) : ℝ :=
  let m := meanOn g C
  (∑ x ∈ C, (g x - m) ^ 2) / (C.card : ℝ)

/-- Root-inclusive expected posterior-variance area of a fixed policy. -/
def policyAreaFrom {n : ℕ} (g : Cube n → ℝ) :
    QueryTree n → Finset (Cube n) → ℝ
  | .leaf, _ => 0
  | .node i left right, C =>
      varianceOn g C +
        (policyAreaFrom g left (childCell C i false) +
          policyAreaFrom g right (childCell C i true)) / 2

def policyArea {n : ℕ} (g : Cube n → ℝ) (t : QueryTree n) : ℝ :=
  policyAreaFrom g t (Finset.univ : Finset (Cube n))

/-- The unrestricted Bellman value, as the infimum over valid complete
coordinate-query trees.  The use of an infimum keeps the statement open and
makes no finiteness or minimizer hypothesis beyond the displayed policy class. -/
def optimalArea {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ t : QueryTree n,
    valid t ∧ complete g t ∧ a = policyArea g t}

def signReal (b : Bool) : ℝ := if b then 1 else -1

def oneExceptionMinus {n : ℕ} (r : Cube n) : Cube n → ℝ :=
  fun x => if x = r then -1 else 1

def oneExceptionPlus {n : ℕ} (r : Cube n) : Cube n → ℝ :=
  fun x => if x = r then 1 else -1

def oneExceptionAreaFormula (n : ℕ) : ℝ :=
  4 * ((2 : ℝ)⁻¹) ^ n * ((n : ℝ) - 1 + ((2 : ℝ)⁻¹) ^ n)

/-- Claim 49753: every complete nonrepeating deterministic policy has the
same one-exception area, and that value is also the unrestricted area. -/
def claim49753_oneExceptionArea : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (r : Cube n) (t : QueryTree n),
      valid t →
      (complete (oneExceptionMinus r) t ∧
        complete (oneExceptionPlus r) t) →
      policyArea (oneExceptionMinus r) t = oneExceptionAreaFormula n ∧
        policyArea (oneExceptionPlus r) t = oneExceptionAreaFormula n ∧
        optimalArea (oneExceptionMinus r) = oneExceptionAreaFormula n ∧
        optimalArea (oneExceptionPlus r) = oneExceptionAreaFormula n

/-- The concrete three-coordinate witness from claim 49761.  Coordinates are
`0 = Z`, `1 = X₁`, and `2 = X₂`; the displayed policy queries `X₁`, then
`X₂`, then `Z`. -/
def witnessT1 : Cube 3 → ℝ := fun x => signReal (x 0)

def witnessT2 : Cube 3 → ℝ := fun x =>
  if x 1 then -signReal (x 2) else signReal (x 2)

def witnessTarget : Cube 3 → ℝ := fun x =>
  (1 / 100 : ℝ) * witnessT1 x + (99 / 100 : ℝ) * witnessT2 x

def witnessPolicy : QueryTree 3 :=
  .node 1
    (.node 2 (.node 0 .leaf .leaf) (.node 0 .leaf .leaf))
    (.node 2 (.node 0 .leaf .leaf) (.node 0 .leaf .leaf))

def shortestHeightWitnessPolicy : QueryTree 3 :=
  .node 0
    (.node 1 (.node 2 .leaf .leaf) (.node 2 .leaf .leaf))
    (.node 1 (.node 2 .leaf .leaf) (.node 2 .leaf .leaf))

/-- The explicit shortest-height obstruction and unrestricted-policy upper
bound in claim 49761. -/
def claim49761_threeCoordinateWitness : Prop :=
  (∀ x : Cube 3, witnessT1 x = -1 ∨ witnessT1 x = 1) ∧
    (∀ x : Cube 3, witnessT2 x = -1 ∨ witnessT2 x = 1) ∧
    valid shortestHeightWitnessPolicy ∧
    complete witnessTarget shortestHeightWitnessPolicy ∧
    policyArea witnessTarget shortestHeightWitnessPolicy = 7351 / 2500 ∧
    (7351 / 2500 : ℝ) > 2 ∧
    valid witnessPolicy ∧
    complete witnessTarget witnessPolicy ∧
    policyArea witnessTarget witnessPolicy ≤ 2 ∧
    optimalArea witnessTarget ≤ 2

end

end MathlibPlus.Open.Probability.ResearchBatch
