import Mathlib
import MathlibPlus.Open.Research.R0333PTEClaims

namespace MathlibPlus.Open.Research.R0333Construction19988

open MathlibPlus.Open.Research.R0333

noncomputable section

/-- The exact arm-shape and arm-count assertions on one literal PTE branch. -/
def pteBranchShape_claim19988
    (α m : ℕ) (p : Fin m → ℕ) (i : Fin m) : Prop :=
  (Finset.filter (fun j : Fin α => j.val < p i)
      (Finset.univ : Finset (Fin α))).card = p i ∧
    (Finset.filter (fun j : Fin α => p i ≤ j.val)
      (Finset.univ : Finset (Fin α))).card = α - p i ∧
    (∀ j : Fin α,
      (∀ e ∈ ptePathArmEdges i j, e ∈ pteEdges α m p) ↔
        j.val < p i) ∧
    (∀ j : Fin α,
      (∀ e ∈ pteStarArmEdges i j, e ∈ pteEdges α m p) ↔
        p i ≤ j.val)

/-- The PTE-tree construction uses the reviewed central/root/arm carrier:
its literal graph is a tree, the centre is joined to every branch root, each
branch has the prescribed path/star arm split, and its order is the stated
`m * (3 * α + 1) + 1`. -/
def claim19988 : Prop :=
  ∀ (α m : ℕ) (p : Fin m → ℕ),
    pteCompatible α m p →
      let G := pteGraph α m p
      G.IsTree ∧
        Fintype.card (PteVertex α m) = pteOrder α m ∧
        (∀ i : Fin m,
          G.Adj (pteCenter (α := α) (m := m))
            (pteBranchRoot i) ∧
          pteBranchShape_claim19988 α m p i)

end

end MathlibPlus.Open.Research.R0333Construction19988
