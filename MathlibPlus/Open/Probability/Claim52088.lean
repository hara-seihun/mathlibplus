import MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support

open scoped BigOperators

namespace MathlibPlus.Open.Probability.Claim52088

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev R4042Sign :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R4293Sign

abbrev R4042Input := Fin 2 → R4042Sign
abbrev R4042BooleanFunction := R4042Input → R4042Sign
abbrev R4042DecisionTree :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R4293DecisionTree

abbrev r4042MinusOne : R4042Sign :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293MinusOne

abbrev r4042PlusOne : R4042Sign :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293PlusOne

abbrev r4042Determines {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293Determines (n := n)

abbrev r4042Queries {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R4293DecisionTree.queries (n := n)

def r4042SignValue (s : R4042Sign) : ℝ :=
  2 * (s.1 : ℝ) - 1

def r4042Input (x₀ x₁ : R4042Sign) : R4042Input :=
  fun i => if i = 0 then x₀ else x₁

def r4042T1 : R4042BooleanFunction :=
  fun x => x 0

def r4042T2 : R4042BooleanFunction :=
  fun x => if x 1 = r4042MinusOne then r4042MinusOne else x 0

def r4042Barycenter : R4042Input → ℝ :=
  fun x =>
    (2 / 3 : ℝ) * r4042SignValue (r4042T1 x) +
      (1 / 3 : ℝ) * r4042SignValue (r4042T2 x)

def r4042BooleanConvexDecomposition {n : ℕ}
    (atoms : Fin n → R4042BooleanFunction) (weights : Fin n → ℝ)
    (target : R4042Input → ℝ) : Prop :=
  (∀ i, 0 ≤ weights i) ∧
    (∑ i : Fin n, weights i = 1) ∧
      ∀ x, ∑ i : Fin n, weights i * r4042SignValue (atoms i x) = target x

noncomputable def r4042AtomMass {n : ℕ}
    (atoms : Fin n → R4042BooleanFunction) (weights : Fin n → ℝ)
    (atom : R4042BooleanFunction) : ℝ :=
  ∑ i : Fin n, if atoms i = atom then weights i else 0

def r4042DisplayedAtoms : Fin 2 → R4042BooleanFunction :=
  fun i => if i = 0 then r4042T1 else r4042T2

def r4042DisplayedWeights : Fin 2 → ℝ :=
  fun i => if i = 0 then (2 / 3 : ℝ) else (1 / 3 : ℝ)

def r4042TreeT1 : R4042DecisionTree 2 :=
  .query 0 (.leaf r4042MinusOne) (.leaf r4042PlusOne)

def r4042TreeT2 : R4042DecisionTree 2 :=
  .query 1 (.leaf r4042MinusOne)
    (.query 0 (.leaf r4042MinusOne) (.leaf r4042PlusOne))

def r4042QueryCount (tree : R4042DecisionTree 2) (x : R4042Input) : ℝ :=
  ∑ i : Fin 2, if r4042Queries tree i x then 1 else 0

def r4042TreeCost (tree : R4042DecisionTree 2) : ℝ :=
  (∑ x : R4042Input, r4042QueryCount tree x) / 4

noncomputable def r4042Q (f : R4042BooleanFunction) : ℝ :=
  sInf {q : ℝ |
    ∃ tree : R4042DecisionTree 2,
      r4042Determines tree f ∧ q = r4042TreeCost tree}

def r4042ExpectedQ {n : ℕ}
    (atoms : Fin n → R4042BooleanFunction) (weights : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, weights i * r4042Q (atoms i)

def claim52088 : Prop :=
  r4042Barycenter (r4042Input r4042MinusOne r4042MinusOne) = -1 ∧
    r4042Barycenter (r4042Input r4042MinusOne r4042PlusOne) = -1 ∧
    r4042Barycenter (r4042Input r4042PlusOne r4042MinusOne) = 1 / 3 ∧
    r4042Barycenter (r4042Input r4042PlusOne r4042PlusOne) = 1 ∧
    r4042Q r4042T1 = 1 ∧
    r4042Q r4042T2 = 3 / 2 ∧
    r4042BooleanConvexDecomposition
      r4042DisplayedAtoms r4042DisplayedWeights r4042Barycenter ∧
    r4042ExpectedQ r4042DisplayedAtoms r4042DisplayedWeights = 7 / 6 ∧
    (∀ (n : ℕ) (atoms : Fin n → R4042BooleanFunction)
        (weights : Fin n → ℝ),
      r4042BooleanConvexDecomposition atoms weights r4042Barycenter →
        (∀ i, 0 < weights i →
          atoms i = r4042T1 ∨ atoms i = r4042T2) ∧
          r4042AtomMass atoms weights r4042T1 = 2 / 3 ∧
          r4042AtomMass atoms weights r4042T2 = 1 / 3) ∧
    (∀ (n : ℕ) (atoms : Fin n → R4042BooleanFunction)
        (weights : Fin n → ℝ),
      r4042BooleanConvexDecomposition atoms weights r4042Barycenter →
        r4042ExpectedQ atoms weights =
          r4042ExpectedQ r4042DisplayedAtoms r4042DisplayedWeights)

end

end MathlibPlus.Open.Probability.Claim52088
