import MathlibPlus.Open.OracleArea.DepthTwoRoofObstruction
import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaSharp.MidpointThreeCube61037

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoNonconvexHull61321

noncomputable section

open scoped BigOperators

abbrev Cube3 := MathlibPlus.Open.OracleArea.Cube 3
abbrev BooleanFunction3 := MathlibPlus.Open.OracleArea.BooleanFunction 3
abbrev Target3 := MathlibPlus.Open.OracleArea.Target 3
abbrev Tree3 := MathlibPlus.Open.OracleArea.DecisionTree 3

private def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

private def h1 : BooleanFunction3 :=
  fun x => if x 2 then Bool.not (x 1) else x 0

private def h2 : BooleanFunction3 :=
  fun x => Bool.not (x 2)

private def h3 : BooleanFunction3 :=
  fun x => if x 0 then Bool.not (x 2) else Bool.not (x 1)

private def h4 : BooleanFunction3 :=
  fun x => x 0

private def h1Formula (x : Cube3) : ℝ :=
  (signValue (x 0) - signValue (x 1) -
      signValue (x 0) * signValue (x 2) -
      signValue (x 1) * signValue (x 2)) / 2

private def h2Formula (x : Cube3) : ℝ :=
  -signValue (x 2)

private def h3Formula (x : Cube3) : ℝ :=
  (-signValue (x 1) - signValue (x 2) +
      signValue (x 0) * signValue (x 1) -
      signValue (x 0) * signValue (x 2)) / 2

private def h4Formula (x : Cube3) : ℝ :=
  signValue (x 0)

private def h1Tree : Tree3 :=
  .node 2
    (.node 0 (.leaf false) (.leaf true))
    (.node 1 (.leaf true) (.leaf false))

private def h2Tree : Tree3 :=
  .node 2 (.leaf true) (.leaf false)

private def h3Tree : Tree3 :=
  .node 0
    (.node 1 (.leaf true) (.leaf false))
    (.node 2 (.leaf true) (.leaf false))

private def h4Tree : Tree3 :=
  .node 0 (.leaf false) (.leaf true)

private def depthTwoAtom (h : BooleanFunction3) : Prop :=
  ∃ t : Tree3, t.depth ≤ 2 ∧ t.represents h

private def atomFormulaFacts : Prop :=
  (∀ x : Cube3,
    MathlibPlus.Open.OracleArea.targetOfBoolean h1 x = h1Formula x) ∧
    (∀ x : Cube3,
      MathlibPlus.Open.OracleArea.targetOfBoolean h2 x = h2Formula x) ∧
      (∀ x : Cube3,
        MathlibPlus.Open.OracleArea.targetOfBoolean h3 x = h3Formula x) ∧
        ∀ x : Cube3,
          MathlibPlus.Open.OracleArea.targetOfBoolean h4 x = h4Formula x

private def atomTreeFacts : Prop :=
  h1Tree.depth ≤ 2 ∧ h1Tree.represents h1 ∧
    h2Tree.depth ≤ 2 ∧ h2Tree.represents h2 ∧
      h3Tree.depth ≤ 2 ∧ h3Tree.represents h3 ∧
        h4Tree.depth ≤ 2 ∧ h4Tree.represents h4

private def atomDistinctFacts : Prop :=
  h1 ≠ h2 ∧ h1 ≠ h3 ∧ h1 ≠ h4 ∧
    h2 ≠ h3 ∧ h2 ≠ h4 ∧ h3 ≠ h4

private def h1Target : Target3 :=
  MathlibPlus.Open.OracleArea.targetOfBoolean h1

private def h2Target : Target3 :=
  MathlibPlus.Open.OracleArea.targetOfBoolean h2

private def h3Target : Target3 :=
  MathlibPlus.Open.OracleArea.targetOfBoolean h3

private def h4Target : Target3 :=
  MathlibPlus.Open.OracleArea.targetOfBoolean h4

private def g1 : Target3 :=
  fun x => (h1Target x + h2Target x) / 2

private def g2 : Target3 :=
  fun x => (h3Target x + h4Target x) / 2

private def g : Target3 :=
  fun x => (g1 x + g2 x) / 2

private def gDirect : Target3 :=
  fun x => (h1Target x + h2Target x + h3Target x + h4Target x) / 4

private def f1 : Target3 :=
  fun x => g1 x / 2

private def f2 : Target3 :=
  fun x => g2 x / 2

private def midpointFacts : Prop :=
  (∀ x : Cube3, g x = (g1 x + g2 x) / 2) ∧
    (∀ x : Cube3, g x = gDirect x)

private def hullRepresentation {m : ℕ} (u : Target3)
    (atoms : Fin m → BooleanFunction3) (weights : Fin m → ℝ) : Prop :=
  (∀ j : Fin m, 0 ≤ weights j) ∧
    (∑ j : Fin m, weights j) = 1 ∧
      (∀ j : Fin m, depthTwoAtom (atoms j)) ∧
        ∀ x : Cube3,
          u x = ∑ j : Fin m,
            weights j * MathlibPlus.Open.OracleArea.targetOfBoolean (atoms j) x

private def inDepthTwoHull (u : Target3) : Prop :=
  ∃ (m : ℕ) (atoms : Fin m → BooleanFunction3) (weights : Fin m → ℝ),
    hullRepresentation u atoms weights

private def depthTwoHull : Set Target3 :=
  {u | inDepthTwoHull u}

private def pairAtoms12 : Fin 2 → BooleanFunction3 :=
  ![h1, h2]

private def pairAtoms34 : Fin 2 → BooleanFunction3 :=
  ![h3, h4]

private def pairWeights : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), 1 / 2]

private def fourAtoms : Fin 4 → BooleanFunction3 :=
  ![h1, h2, h3, h4]

private def fourWeights : Fin 4 → ℝ :=
  ![(1 / 4 : ℝ), 1 / 4, 1 / 4, 1 / 4]

private def constantTrue : BooleanFunction3 :=
  MathlibPlus.Open.OracleArea.constant3 true

private def constantFalse : BooleanFunction3 :=
  MathlibPlus.Open.OracleArea.constant3 false

private def scaledAtoms1 : Fin 4 → BooleanFunction3 :=
  ![h1, h2, constantTrue, constantFalse]

private def scaledAtoms2 : Fin 4 → BooleanFunction3 :=
  ![h3, h4, constantTrue, constantFalse]

private def hullWitnessFacts : Prop :=
  hullRepresentation g1 pairAtoms12 pairWeights ∧
    hullRepresentation g2 pairAtoms34 pairWeights ∧
      hullRepresentation g fourAtoms fourWeights ∧
        hullRepresentation f1 scaledAtoms1 fourWeights ∧
          hullRepresentation f2 scaledAtoms2 fourWeights

noncomputable def bellmanArea (u : Target3) : ℝ :=
  MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaSharp.A3 u

private def areaFacts : Prop :=
  bellmanArea g1 = 3 / 4 ∧
    bellmanArea g2 = 3 / 4 ∧
      bellmanArea g = 49 / 64 ∧
        bellmanArea g -
            (bellmanArea g1 + bellmanArea g2) / 2 = 1 / 64 ∧
          0 < bellmanArea g -
            (bellmanArea g1 + bellmanArea g2) / 2

private def atomAreaFacts : Prop :=
  bellmanArea h1Target = 2 ∧
    bellmanArea h2Target = 1 ∧
      bellmanArea h3Target = 2 ∧
        bellmanArea h4Target = 1 ∧
          (2 + 1 + 2 + 1 : ℝ) / 4 ≥ bellmanArea g

private def scalingFacts : Prop :=
  (∀ x : Cube3, f1 x + f2 x = g x) ∧
    bellmanArea f1 = 3 / 16 ∧
      bellmanArea f2 = 3 / 16 ∧
        bellmanArea (fun x => f1 x + f2 x) = 49 / 64 ∧
          Real.sqrt (bellmanArea (fun x => f1 x + f2 x)) = 7 / 8 ∧
            Real.sqrt (bellmanArea f1) + Real.sqrt (bellmanArea f2) =
              Real.sqrt 3 / 2 ∧
              Real.sqrt (bellmanArea (fun x => f1 x + f2 x)) >
                Real.sqrt (bellmanArea f1) + Real.sqrt (bellmanArea f2)

private def dependsOn (u : Target3) (i : Fin 3) : Prop :=
  ∃ x : Cube3,
    u x ≠ u (Function.update x i (Bool.not (x i)))

private def sharedAllCoordinates : Prop :=
  ∀ i : Fin 3, dependsOn f1 i ∧ dependsOn f2 i

private def areaConvexOnHull : Prop :=
  ConvexOn ℝ depthTwoHull bellmanArea

private def sqrtAreaSubadditiveOnHull : Prop :=
  ∀ u v : Target3,
    u ∈ depthTwoHull →
      v ∈ depthTwoHull →
        Real.sqrt (bellmanArea (fun x => u x + v x)) ≤
          Real.sqrt (bellmanArea u) + Real.sqrt (bellmanArea v)

/-- Claim 61321: the exact three-coordinate four-atom Bellman witness lies in
 the convex hull of depth-at-most-two Boolean decision-tree targets, has the
 displayed strict midpoint defect, and gives the overlapping square-root
 subadditivity obstruction without exceeding area two. -/
def claim61321_depthTwoHullNonconvexity : Prop :=
  atomFormulaFacts ∧
    atomTreeFacts ∧
      atomDistinctFacts ∧
        (depthTwoAtom h1 ∧ depthTwoAtom h2 ∧
          depthTwoAtom h3 ∧ depthTwoAtom h4) ∧
          hullWitnessFacts ∧
            (inDepthTwoHull g1 ∧ inDepthTwoHull g2 ∧
              inDepthTwoHull g ∧ inDepthTwoHull f1 ∧ inDepthTwoHull f2) ∧
              midpointFacts ∧
                areaFacts ∧
                  ¬ areaConvexOnHull ∧
                    scalingFacts ∧
                      ¬ sqrtAreaSubadditiveOnHull ∧
                        sharedAllCoordinates ∧
                          atomAreaFacts ∧
                            bellmanArea g < 2

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoNonconvexHull61321
