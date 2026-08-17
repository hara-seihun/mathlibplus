import MathlibPlus.Open.Combinatorics.Claim59963DecisionTreeProfile

namespace MathlibPlus.Open.Combinatorics.AllOrdersMaximumLoad

open scoped BigOperators

noncomputable section

/-- A Boolean decision tree is a real-valued tree whose outputs are the two signs. -/
def isBooleanDecisionTree {S : Type*} (tree : DecisionTree S) : Prop :=
  ∀ x : SpinCube S, tree.eval x = 1 ∨ tree.eval x = -1

/-- A finite convex mixture of Boolean trees with a common depth bound. -/
structure FiniteBooleanTreeMixture (S : Type*) [Fintype S] (d : ℕ) where
  entries : List (DecisionTree S × ℝ)
  weight_nonnegative : ∀ entry ∈ entries, 0 ≤ entry.2
  weight_sum : (entries.map (fun entry => entry.2)).sum = 1
  depth_bound : ∀ entry ∈ entries, entry.1.depth ≤ d
  boolean_entries : ∀ entry ∈ entries, isBooleanDecisionTree entry.1

def mixtureValue {S : Type*} [Fintype S] {d : ℕ}
    (mixture : FiniteBooleanTreeMixture S d)
    (x : SpinCube S) : ℝ :=
  (mixture.entries.map (fun entry => entry.2 * entry.1.eval x)).sum

/-- The normalized one-coordinate Rademacher derivative. -/
def coordinateDerivative {S : Type*} [Fintype S] (i : S)
    (f : SpinCube S → ℝ) (x : SpinCube S) : ℝ := by
  classical
  exact
    (f (fun j => if j = i then true else x j) -
      f (fun j => if j = i then false else x j)) / 2

/-- The order-independent mixed derivative, written as its alternating sum. -/
def mixedDerivative {S : Type*} [Fintype S] (U : Finset S)
    (f : SpinCube S → ℝ) (x : SpinCube S) : ℝ :=
  clampedDerivativeSet U f x

/-- The all-order derivative mass attached to a coordinate set. -/
noncomputable def hU {S : Type*} [Fintype S] (U : Finset S)
    (f : SpinCube S → ℝ) : ℝ :=
  cubeExpectation (fun x => |mixedDerivative U f x|)

/-- The sum of the derivative masses over all coordinate sets. -/
noncomputable def totalH {S : Type*} [Fintype S]
    (f : SpinCube S → ℝ) : ℝ := by
  classical
  exact ∑ U : Finset S, hU U f

/-- The derivative load carried by one coordinate. -/
noncomputable def coordinateLoad {S : Type*} [Fintype S] (i : S)
    (f : SpinCube S → ℝ) : ℝ := by
  classical
  exact ∑ U : Finset S, if i ∈ U then hU U f else 0

/-- Variance for the uniform finite Rademacher cube. -/
noncomputable def cubeVariance {S : Type*} [Fintype S]
    (f : SpinCube S → ℝ) : ℝ :=
  cubeExpectation (fun x => (f x - cubeExpectation f) ^ 2)

/-- The maximum coordinate load on a nonempty finite coordinate set. -/
noncomputable def maximumCoordinateLoad {S : Type*} [Fintype S] [Nonempty S]
    (f : SpinCube S → ℝ) : ℝ := by
  classical
  exact Finset.sup' (Finset.univ : Finset S) Finset.univ_nonempty
    (fun i => coordinateLoad i f)

noncomputable def loadRatio {S : Type*} [Fintype S] [Nonempty S]
    (f : SpinCube S → ℝ) : ℝ :=
  ((1 + totalH f) * cubeVariance f) / maximumCoordinateLoad f

/-- Claim 61017: the all-orders maximum-load ratio is unbounded in the finite
Rademacher-cube convex-mixture class. -/
def claim61017 : Prop :=
  (∀ d : ℕ, 1 ≤ d →
    ∃ n : ℕ,
      ∃ mixture : FiniteBooleanTreeMixture (Fin (n + 1)) d,
        let f := mixtureValue mixture
        (∀ x, |f x| ≤ 1) ∧
          loadRatio f ≥ (2 : ℝ) ^ ((d : ℤ) - 2)) ∧
    ¬ ∃ C : ℝ,
      ∀ (S : Type*) [Fintype S] [Nonempty S] (d : ℕ)
        (mixture : FiniteBooleanTreeMixture S d),
        (1 + totalH (mixtureValue mixture)) *
              cubeVariance (mixtureValue mixture) ≤
          C * maximumCoordinateLoad (mixtureValue mixture)

end

end MathlibPlus.Open.Combinatorics.AllOrdersMaximumLoad
