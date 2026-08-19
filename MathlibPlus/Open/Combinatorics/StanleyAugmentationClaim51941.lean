import MathlibPlus.Open.Combinatorics.Claims51949_51951

namespace MathlibPlus.Open.Combinatorics.StanleyAugmentation

/-- Isomorphism of the underlying tree graphs that carries the first root to
    the second root. -/
def rootedTreeIsoAt {V : Type*}
    (T : SimpleGraph V) (v w : V) : Prop :=
  ∃ e : T ≃g T, e.toEquiv v = w

/-- Claim 51941: the U-polynomial of a one-leaf augmentation identifies the
    rooted tree, equivalently the automorphism orbit of its attachment vertex. -/
def augmentationValueRootRigidity_claim51941 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V),
    T.IsTree →
    ∀ v w : V,
      (augmentationValue T v = augmentationValue T w ↔
        rootedTreeIsoAt T v w) ∧
      (rootedTreeIsoAt T v w ↔
        MathlibPlus.Open.Combinatorics.DTreeUPolynomial.rootOrbit T v w)

end MathlibPlus.Open.Combinatorics.StanleyAugmentation
