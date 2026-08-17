import MathlibPlus.Open.ResearchFormalization.R3720TreeU

namespace MathlibPlus.Open.ResearchFormalization.R3720

noncomputable section

open MathlibPlus.Open.TreeSpectral

/-- Claim 48411: the rational unlabelled-tree spaces carry the exact leaf
    deletion, all-vertex leaf-grafting, and U-polynomial maps, with the first
    pendant moment given by `U_(n-1) ∘ L_n`. -/
def claim_48411 : Prop :=
  (∀ (n : ℕ) (T : TreeClass n),
    leafDeletion n (Finsupp.single T 1) = leafDeletionBasis n T) ∧
  (∀ (n : ℕ) (T : TreeClass n),
    graft n (Finsupp.single T 1) = graftBasis n T) ∧
  (∀ (n : ℕ) (T : TreeClass n),
    uMap n (Finsupp.single T 1) = treeUPolynomial T) ∧
  (∀ (n : ℕ) (w : TreeSpace n),
    weightHomogeneous n (uMap n w)) ∧
  (∀ (n : ℕ),
    momentMap n = (uMap (n - 1)).comp (leafDeletion n))

end

end MathlibPlus.Open.ResearchFormalization.R3720
