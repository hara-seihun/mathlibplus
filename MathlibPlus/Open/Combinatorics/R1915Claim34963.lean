import MathlibPlus.Open.Combinatorics.R1915Claim34961

namespace MathlibPlus.Open.Combinatorics.R1915Claim34963

open MathlibPlus.Open.Combinatorics.R1915Claim34961

/-- The directed edge selected by the outside-corner displacement. -/
def outsideCornerPlane {n : ℕ}
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3) (i j : Fin n) : Prop :=
  directionalDisplacement F i j ∉ cornerPlane (A i) (F i zeroCube)

/-- The orientation relation on distinct directions. -/
def orientationRelation {n : ℕ}
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3) (i j : Fin n) : Prop :=
  i ≠ j ∧ outsideCornerPlane F A i j

/-- Exactly one directed edge is present on each distinct pair in `H`. -/
def tournamentOn {n : ℕ} (H : Finset (Fin n))
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3) : Prop :=
  ∀ i : Fin n, i ∈ H → ∀ j : Fin n, j ∈ H → i ≠ j →
    (orientationRelation F A i j ∨ orientationRelation F A j i) ∧
      ¬ (orientationRelation F A i j ∧ orientationRelation F A j i)

/-- Claim 34963: for every distinct pair of heavy missing-corner directions,
exactly one displacement is outside its corner plane, and the displacement in
the reverse direction is nonzero and in that reverse corner plane.  The
outside displacement orients the resulting tournament on `H`. -/
def claim34963 : Prop :=
  ∀ (n : ℕ) (H : Finset (Fin n))
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3)
    (E : Fin n → Cube n → Prop),
    missingCornerData H F A E →
      c4Free E →
        (∀ i : Fin n, i ∈ H → ∀ j : Fin n, j ∈ H → i ≠ j →
          ((outsideCornerPlane F A i j ∧
              inPlaneNonzero F A j (directionalDisplacement F j i)) ∨
            (outsideCornerPlane F A j i ∧
              inPlaneNonzero F A i (directionalDisplacement F i j))) ∧
            (outsideCornerPlane F A i j ∨ outsideCornerPlane F A j i) ∧
            ¬ (outsideCornerPlane F A i j ∧ outsideCornerPlane F A j i)) ∧
        tournamentOn H F A

end MathlibPlus.Open.Combinatorics.R1915Claim34963
