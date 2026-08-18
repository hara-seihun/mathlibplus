import MathlibPlus.Open.ResearchFormalization.RademacherArea

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaCommonOptimalRootSquareDepth

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Worst-case depth of a deterministic coordinate decision tree. -/
def treeDepth : DecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue =>
      1 + max (treeDepth ifFalse) (treeDepth ifTrue)

/-- A tree contains no query of `i`, so it is a legal tree for a section after
that coordinate has been fixed. -/
def avoidsCoordinate (i : Fin n) : DecisionTree n → Prop
  | .leaf _ => True
  | .query coordinate ifFalse ifTrue =>
      coordinate ≠ i ∧
        avoidsCoordinate i ifFalse ∧ avoidsCoordinate i ifTrue

/-- The root-query condition used by the common-root hypothesis. -/
def rootedAt (i : Fin n) : DecisionTree n → Prop
  | .leaf _ => False
  | .query coordinate _ _ => coordinate = i

/-- The section of a Boolean atom obtained by fixing `X_i` to `σ`. -/
def sectionValue (h : BooleanFunction n) (i : Fin n) (σ : Bool)
    (x : RademacherCube n) : ℝ :=
  h.1 (Function.update x i σ)

/-- The minimum legal worst-case depth of a deterministic tree computing an
atom. -/
noncomputable def minimumDepth (h : BooleanFunction n) : ℕ :=
  sInf {d : ℕ |
    ∃ t : DecisionTree n,
      validDeterminingTree h t ∧ treeDepth t = d}

/-- The corresponding minimum depth after fixing one coordinate, with the
remaining tree forbidden to query that coordinate. -/
noncomputable def sectionDepth (h : BooleanFunction n) (i : Fin n) (σ : Bool) : ℕ :=
  sInf {d : ℕ |
    ∃ t : DecisionTree n,
      noRepeat t ∧
        (∀ x : RademacherCube n,
          t.evaluate x = sectionValue h i σ x) ∧
        avoidsCoordinate i t ∧
        treeDepth t = d}

/-- Nonconstancy of an atom on the uniform cube. -/
def atomConstant (h : BooleanFunction n) : Prop :=
  ∃ c : ℝ, ∀ x : RademacherCube n, h.1 x = c

/-- Every positive-mass nonconstant atom has a minimum-depth determining tree
whose root query is the same coordinate `i`. A finite list is sufficient here:
the cube is finite, so an arbitrary finite or countably supported law on its
Boolean atoms has an equivalent finite mass law after equal atoms are merged. -/
def commonOptimalRoot (law : BooleanLaw n) (i : Fin n) : Prop :=
  ∀ entry ∈ law,
    0 < entry.2 →
      ¬ atomConstant entry.1 →
        ∃ t : DecisionTree n,
          validDeterminingTree entry.1 t ∧
            rootedAt i t ∧
              treeDepth t = minimumDepth entry.1

/-- The square-root depth reserve averaged over the atom law. -/
noncomputable def depthReserve (law : BooleanLaw n) : ℝ :=
  (law.map (fun entry =>
    entry.2 * Real.sqrt (minimumDepth entry.1 : ℝ))).sum

/-- The square-root reserve after conditioning the common root to `σ`. -/
noncomputable def sectionDepthReserve (law : BooleanLaw n)
    (i : Fin n) (σ : Bool) : ℝ :=
  (law.map (fun entry =>
    entry.2 * Real.sqrt (sectionDepth entry.1 i σ : ℝ))).sum

/-- Variance of the fixed mixture mean on the uniform independent-sign cube. -/
noncomputable def mixtureVariance (law : BooleanLaw n) : ℝ :=
  let g := lawBarycenter law
  uniformMean (fun x => (g x - uniformMean g) ^ 2)

/-- Claim 61224: a common minimum-depth root makes the square-root depth
reserve pay one sharp Bellman step. -/
def claim61224 : Prop :=
  ∀ (n : ℕ) (law : BooleanLaw n) (i : Fin n),
    isProbabilityLaw law →
      commonOptimalRoot law i →
        mixtureVariance law +
            (sectionDepthReserve law i false ^ 2 +
              sectionDepthReserve law i true ^ 2) / 2 ≤
          depthReserve law ^ 2

end

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaCommonOptimalRootSquareDepth
