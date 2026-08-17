import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1066Claim29967

noncomputable section

/-- The eight nonzero vectors of the pointed base `𝔽₃²`. -/
abbrev Base := Fin 2 → ZMod 3

/-- The linear automorphism carrier `GL(2,3)`. -/
abbrev GL2_3 := Base ≃ₗ[ZMod 3] Base

/-- Base permutations fixing the zero vector. -/
abbrev PointedBaseMap := {σ : Base ≃ Base // σ 0 = 0}

/-- The possible active marked base point. -/
abbrev ActiveBasePoint := {c : Base // c ≠ 0}

/-- The complete marked base-map space. -/
abbrev MarkedBaseMap := PointedBaseMap × ActiveBasePoint

/-- The displayed pre- and postcomposition action, with the marked point
transported by the right linear change of coordinates. -/
def markedBaseMapAction (L R : GL2_3)
    (p q : MarkedBaseMap) : Prop :=
  (∀ x : Base, q.1.1 x = L (p.1.1 (R.symm x))) ∧
    q.2.1 = R p.2.1

/-- Claim 29967: the pointed permutation and nonzero-vector carriers, their
exact cardinality, and the `GL(2,3)` double-coset action are explicit. -/
def claim29967 : Prop :=
  Nat.card MarkedBaseMap = Nat.factorial 8 * 8 ∧
    Nat.card MarkedBaseMap = 322560 ∧
    ∀ L R : GL2_3, ∀ p : MarkedBaseMap,
      ∃! q : MarkedBaseMap, markedBaseMapAction L R p q

end

end MathlibPlus.Open.ResearchFormalization.R1066Claim29967
