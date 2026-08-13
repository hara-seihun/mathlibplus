import Mathlib

namespace MathlibPlus.Geometry.Claim34433

/-- The four direction labels used by the crossing construction. -/
inductive Direction where
  | u
  | v
  | w
  | b
  deriving DecidableEq

open Direction

/-- The projective distances specified in claim 34433.  The source uses only
these six unordered pairs, so the symmetric table is made explicit. -/
noncomputable def projectiveDistance : Direction → Direction → ℝ
  | u, u => 0
  | u, v => 2 * Real.pi / 5
  | u, w => Real.pi / 10
  | u, b => Real.pi / 2
  | v, u => 2 * Real.pi / 5
  | v, v => 0
  | v, w => Real.pi / 2
  | v, b => Real.pi / 10
  | w, u => Real.pi / 10
  | w, v => Real.pi / 2
  | w, w => 0
  | w, b => 2 * Real.pi / 5
  | b, u => Real.pi / 2
  | b, v => Real.pi / 10
  | b, w => 2 * Real.pi / 5
  | b, b => 0

def crosses (x y : Direction) : Prop :=
  projectiveDistance x y > Real.pi / 3

/-- The exact distance table in claim 34433. -/
theorem pairwiseDistances_claim34433 :
    projectiveDistance u v = 2 * Real.pi / 5 ∧
      projectiveDistance w b = 2 * Real.pi / 5 ∧
      projectiveDistance u b = Real.pi / 2 ∧
      projectiveDistance w v = Real.pi / 2 ∧
      projectiveDistance u w = Real.pi / 10 ∧
      projectiveDistance v b = Real.pi / 10 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exactly the four cyclic pairs cross the `π/3` threshold. -/
theorem crossingPairs_claim34433 :
    ∀ x y, x ≠ y →
      (crosses x y ↔
        ((x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨
         (x = v ∧ y = w) ∨ (x = w ∧ y = v) ∨
         (x = w ∧ y = b) ∨ (x = b ∧ y = w) ∨
         (x = b ∧ y = u) ∨ (x = u ∧ y = b))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have huv : 2 * Real.pi / 5 > Real.pi / 3 := by nlinarith
  have hub : Real.pi / 2 > Real.pi / 3 := by nlinarith
  have huw : ¬(Real.pi / 10 > Real.pi / 3) := by nlinarith
  intro x y hxy
  cases x <;> cases y <;>
    simp_all [crosses, projectiveDistance, huv, hub, huw]

/-- The same-family pairs in the construction do not cross. -/
theorem sameFamily_nonCrossing_claim34433 :
    ¬ crosses u w ∧ ¬ crosses v b := by
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor <;> dsimp [crosses, projectiveDistance] <;> nlinarith

/-- The crossing relation is the adjacency relation of the four-cycle
`u-v-w-b-u`. -/
def crossingGraph : SimpleGraph Direction where
  Adj := crosses
  symm := ⟨by
    intro x y hxy
    cases x <;> cases y <;>
      simpa [crosses, projectiveDistance] using hxy⟩
  loopless := ⟨by
    intro x
    cases x <;> dsimp [crosses, projectiveDistance] <;> nlinarith [Real.pi_pos]⟩

theorem crossingGraph_edges_claim34433 (x y : Direction) (hxy : x ≠ y) :
    crossingGraph.Adj x y ↔
      ((x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨
       (x = v ∧ y = w) ∨ (x = w ∧ y = v) ∨
       (x = w ∧ y = b) ∨ (x = b ∧ y = w) ∨
       (x = b ∧ y = u) ∨ (x = u ∧ y = b)) := by
  exact crossingPairs_claim34433 x y hxy

end MathlibPlus.Geometry.Claim34433
