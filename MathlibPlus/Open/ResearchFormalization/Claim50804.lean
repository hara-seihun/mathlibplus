import MathlibPlus.Open.ResearchFormalization.RademacherArea

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim50804

noncomputable section

open MathlibPlus.Open.ResearchFormalization

/-- The number of oracle queries made along a Boolean decision-tree path. -/
def queryCount {n : ℕ} : DecisionTree n → RademacherCube n → ℕ
  | .leaf _, _ => 0
  | .query coordinate ifFalse ifTrue, x =>
      1 + if x coordinate then queryCount ifTrue x else queryCount ifFalse x

/-- Uniform expected query cost of a deterministic tree. -/
def expectedQueryCost {n : ℕ} (tree : DecisionTree n) : ℝ :=
  (∑ x : RademacherCube n, (queryCount tree x : ℝ)) / (2 : ℝ) ^ n

/-- The displayed root of a decision tree. -/
def rootCoordinate {n : ℕ} : DecisionTree n → Option (Fin n)
  | .leaf _ => none
  | .query coordinate _ _ => some coordinate

/-- The posterior mean of an arbitrary real target at a displayed tree node. -/
def targetNodeMean {n : ℕ} (g : RademacherCube n → ℝ)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  (transcriptCell tree path).sum g /
    ((transcriptCell tree path).card : ℝ)

/-- The posterior variance at a displayed tree node. -/
def targetNodeVariance {n : ℕ} (g : RademacherCube n → ℝ)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  (transcriptCell tree path).sum
      (fun x => (g x - targetNodeMean g tree path) ^ 2) /
    ((transcriptCell tree path).card : ℝ)

/-- Root-inclusive posterior-variance area of a deterministic tree. -/
def targetPolicyArea {n : ℕ} (g : RademacherCube n → ℝ)
    (tree : DecisionTree n) : ℝ :=
  tree.internalPaths.sum (fun path =>
    ((transcriptCell tree path).card : ℝ) / (2 : ℝ) ^ n *
      targetNodeVariance g tree path)

/-- Minimum expected query cost among nonrepeating determining trees. -/
noncomputable def queryCost {n : ℕ} (h : BooleanFunction n) : ℝ :=
  sInf {c : ℝ |
    ∃ tree : DecisionTree n,
      validDeterminingTree h tree ∧ c = expectedQueryCost tree}

/-- A tree in the minimum-cost root set of a Boolean target. -/
def minimumCostRoot {n : ℕ} (h : BooleanFunction n) (i : Fin n) : Prop :=
  ∃ tree : DecisionTree n,
    validDeterminingTree h tree ∧
      rootCoordinate tree = some i ∧
      expectedQueryCost tree = queryCost h

/-- The minimum area over minimum-query-cost policies with a prescribed root. -/
noncomputable def rootContinuationArea {n : ℕ} (h : BooleanFunction n)
    (g : RademacherCube n → ℝ) (i : Fin n) : ℝ :=
  sInf {a : ℝ |
    ∃ tree : DecisionTree n,
      validDeterminingTree h tree ∧
        expectedQueryCost tree = queryCost h ∧
        rootCoordinate tree = some i ∧
        a = targetPolicyArea g tree}

/-- The S6 root choice: a minimum-cost root attaining the target-dependent
minimum of the q-optimal continuation area. -/
def targetMinimizingRoot {n : ℕ} (h : BooleanFunction n)
    (g : RademacherCube n → ℝ) (i : Fin n) : Prop :=
  minimumCostRoot h i ∧
    ∀ j : Fin n, minimumCostRoot h j →
      rootContinuationArea h g i ≤ rootContinuationArea h g j

/-- A nonconstant Boolean atom on the finite unbiased cube. -/
def nonconstant {n : ℕ} (h : BooleanFunction n) : Prop :=
  ∃ x y : RademacherCube n, h.1 x ≠ h.1 y

/-- A finite positive law on all-nonconstant Boolean atoms, represented by its
finite support and its masses. -/
def allNonconstantLaw {n m : ℕ}
    (atoms : Fin m → BooleanFunction n) (weights : Fin m → ℝ) : Prop :=
  (∀ j : Fin m, 0 ≤ weights j) ∧
    (∑ j : Fin m, weights j = 1) ∧
    (∀ j : Fin m, 0 < weights j → nonconstant (atoms j))

/-- The law barycentre. -/
def lawBarycenter {n m : ℕ} (atoms : Fin m → BooleanFunction n)
    (weights : Fin m → ℝ) : RademacherCube n → ℝ :=
  fun x => ∑ j : Fin m, weights j * (atoms j).1 x

/-- The mass of the class of atoms assigned root `i`. -/
def rootClassMass {n m : ℕ} (weights : Fin m → ℝ)
    (roots : Fin m → Fin n) (i : Fin n) : ℝ :=
  ∑ j : Fin m, if roots j = i then weights j else 0

/-- The conditional class barycentre.  At an empty class the inverse of
its zero mass makes the extended value zero; its weighted contribution is
therefore exactly the omitted empty-class contribution. -/
def rootClassBarycenter {n m : ℕ}
    (atoms : Fin m → BooleanFunction n) (weights : Fin m → ℝ)
    (roots : Fin m → Fin n) (i : Fin n)
    (x : RademacherCube n) : ℝ :=
  (rootClassMass weights roots i)⁻¹ *
    ∑ j : Fin m,
      if roots j = i then weights j * (atoms j).1 x else 0

/-- Claim 50804: target-minimizing minimum-cost roots induce the exact
barycentric discrepancy cancellation, while an arbitrary target retains the
corresponding affine barycentre identity. -/
def claim50804 : Prop :=
  ∀ (n m : ℕ) (atoms : Fin m → BooleanFunction n)
    (weights : Fin m → ℝ) (roots : Fin m → Fin n),
    allNonconstantLaw atoms weights →
      let u := lawBarycenter atoms weights
      (∀ j : Fin m, 0 < weights j →
        targetMinimizingRoot (atoms j) u (roots j)) →
        (∀ x : RademacherCube n,
          ∑ i : Fin n,
            rootClassMass weights roots i *
              (u x - rootClassBarycenter atoms weights roots i x) = 0) ∧
        (∀ (g : RademacherCube n → ℝ) (x : RademacherCube n),
          ∑ i : Fin n,
            rootClassMass weights roots i *
              (g x - rootClassBarycenter atoms weights roots i x) =
                g x - u x)

end

end MathlibPlus.Open.ResearchFormalization.Claim50804
