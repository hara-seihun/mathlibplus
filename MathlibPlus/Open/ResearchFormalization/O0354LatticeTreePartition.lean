import MathlibPlus.Combinatorics.Claim44521
import MathlibPlus.Open.Combinatorics.NR2OrderedEdgePartition

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0354

noncomputable section

open MathlibPlus.Combinatorics.Claim44521
open MathlibPlus.Open.Combinatorics.NR2

abbrev UnlabeledGraph (n : ℕ) := finiteSimpleGraphType n

noncomputable def graphRepresentative {n : ℕ} (Y : UnlabeledGraph n) :
    SimpleGraph (Fin n) :=
  Quotient.out Y

/-- The exact carrier of unlabeled twelve-vertex trees at edge level eleven. -/
def TreeType12 :=
  {Y : UnlabeledGraph 12 //
    (graphRepresentative Y).IsTree ∧
      (graphEdgeFinset (graphRepresentative Y)).card = 11}

noncomputable instance treeType12Finite : Finite TreeType12 :=
  Finite.of_injective (f := fun T : TreeType12 => T.1)
    Subtype.val_injective

noncomputable instance treeType12Fintype : Fintype TreeType12 :=
  Fintype.ofFinite _

noncomputable def treePartitionPolynomial (T : TreeType12) :
    MvPolynomial (Set FiniteGraph) ℤ :=
  orderedEdgePartitionPolynomial (graphRepresentative T.1)

noncomputable def weightedSupport (w : TreeType12 → ℤ) : Finset TreeType12 := by
  classical
  exact Finset.univ.filter (fun T => w T ≠ 0)

noncomputable def touchedPartitionSignatures (w : TreeType12 → ℤ) :
    Finset ((Set FiniteGraph) →₀ ℕ) := by
  classical
  exact (weightedSupport w).biUnion
    (fun T => (treePartitionPolynomial T).support)

noncomputable def foldedPartitionPolynomial (w : TreeType12 → ℤ) :
    MvPolynomial (Set FiniteGraph) ℤ :=
  ∑ T : TreeType12, MvPolynomial.C (w T) * treePartitionPolynomial T

/-- Claim 15602: the exact order-twelve, eleven-edge tree columns have an
integer dependence supported on 105 of the 551 trees, with coefficients of
absolute value one, two, or three; its fold touches exactly 4,986 signatures
and every folded coefficient vanishes. -/
def claim15602_latticeTreePartitionNullRelation : Prop :=
  Fintype.card TreeType12 = 551 ∧
    ∃ w : TreeType12 → ℤ,
      w ≠ 0 ∧
        (weightedSupport w).card = 105 ∧
          (∀ T : TreeType12, w T ≠ 0 →
            Int.natAbs (w T) = 1 ∨
              Int.natAbs (w T) = 2 ∨ Int.natAbs (w T) = 3) ∧
            (touchedPartitionSignatures w).card = 4986 ∧
              foldedPartitionPolynomial w = 0 ∧
                (∀ σ : (Set FiniteGraph) →₀ ℕ,
                  MvPolynomial.coeff σ (foldedPartitionPolynomial w) = 0)

end

end MathlibPlus.Open.ResearchFormalization.O0354
