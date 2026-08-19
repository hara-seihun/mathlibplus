import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Rank5AffineTwist61380

noncomputable section

abbrev C9 := ZMod 9

/-- The binary direct-sum coordinate model `W ⊕ C`, represented as `W × C`.
The first coordinate is the active three-space `W`, and the second is the
complementary two-space `C`. -/
abbrev V (W C : Type*) := W × C

abbrev G (W C : Type*) := V W C × C9

/-- The cyclic section of a connection set over a binary direction. -/
def sectionSet {W C : Type*}
    [Zero W] [Zero C]
    (S : Set (G W C)) (v : V W C) : Set C9 :=
  {z | (v, z) ∈ S}

/-- The additive Cayley adjacency relation used for the ordinary undirected
Cayley graphs in the claim. -/
def cayleyAdjacency {W C : Type*}
    [AddGroup W] [AddGroup C]
    (S : Set (G W C)) (x y : G W C) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- A pointed ordinary Cayley-graph isomorphism that preserves the standard
partition into the `C₉` fibres, allowing an arbitrary permutation of the
binary directions. -/
def pointedStandardC9FibreIsomorphism {W C : Type*}
    [AddGroup W] [AddGroup C]
    (S T : Set (G W C)) (f : G W C ≃ G W C) : Prop :=
  f 0 = 0 ∧
    (∀ x y : G W C,
      cayleyAdjacency S x y ↔
        cayleyAdjacency T (f x) (f y)) ∧
      ∃ β : V W C ≃ V W C,
        ∀ v : V W C, ∀ z : C9,
          (f (v, z)).1 = β v

/-- The order-three linear part in the displayed fibrewise affine chart. -/
def fixedSpace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (M : W ≃ₗ[ZMod 2] W) : Submodule (ZMod 2) W :=
  LinearMap.ker (M.toLinearMap - LinearMap.id)

/-- The exact affine chart from the admitted claim.  In the product model for
`W ⊕ C`, the source point `c + w` is `(w,c)`. -/
def affineTwistForm {W C : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup C]
    (M : W ≃ₗ[ZMod 2] W)
    (π : C ≃ C) (a : C → W) (b : C → C9) (k : C → ZMod 3)
    (f : G W C ≃ G W C) : Prop :=
  ∀ (c : C) (w : W) (z : C9),
    f ((w, c), z) =
      (((M ^ (k c).val) w + a c, π c),
        (4 : C9) ^ (k c).val * z + b c)

/-- The order-three subgroup `3 C₉` appearing in the periodic-fibre
hypothesis. -/
def threeC9 : Set C9 :=
  {h | ∃ y : C9, h = 3 * y}

/-- Translation-periodicity by `3 C₉` for one cyclic section. -/
def threePeriodicSection (D : Set C9) : Prop :=
  ∀ (z h : C9), h ∈ threeC9 → (z ∈ D ↔ z + h ∈ D)

/-- Every source section over a nonzero complementary-coordinate coset is
`3 C₉`-periodic. -/
def sourceThreePeriodic {W C : Type*}
    [AddGroup W] [AddGroup C]
    (S : Set (G W C)) : Prop :=
  ∀ (c : C), c ≠ 0 →
    ∀ (w : W), threePeriodicSection (sectionSet S (w, c))

/-- The section equality in the ordinary-CI conclusion. -/
def sectionTransport {W C : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup C] [Module (ZMod 2) C]
    (S T : Set (G W C)) (L : V W C ≃ₗ[ZMod 2] V W C)
    (u : C9ˣ) : Prop :=
  ∀ v : V W C,
    sectionSet T (L v) =
      Set.image (fun z : C9 => (u : C9) * z) (sectionSet S v)

/-- The product map corresponding to a binary linear shadow and a cyclic
unit multiplier. -/
def productTransport {W C : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup C] [Module (ZMod 2) C]
    (L : V W C ≃ₗ[ZMod 2] V W C) (u : C9ˣ) : G W C → G W C :=
  fun p => (L p.1, (u : C9) * p.2)

/-- Claim 61380: the rank-five `W ≅ F₂^3`, `C ≅ F₂^2` standard-`C₉`-fibre
order-three affine-twist chart always has a common linear/unit shadow on the
connection-set sections, and therefore an additive product transporter. -/
def claim61380 : Prop :=
  ∀ (W C : Type*)
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    [AddCommGroup C] [Module (ZMod 2) C]
    [FiniteDimensional (ZMod 2) C],
    Module.finrank (ZMod 2) W = 3 →
      Module.finrank (ZMod 2) C = 2 →
      ∀ (M : W ≃ₗ[ZMod 2] W),
        orderOf M = 3 →
          Module.finrank (ZMod 2) (fixedSpace M) = 1 →
            ∀ (S T : Set (G W C)),
              S ⊆ (Set.univ : Set (G W C)) \ ({0} : Set (G W C)) →
                T ⊆ (Set.univ : Set (G W C)) \ ({0} : Set (G W C)) →
                  (∀ x : G W C, x ∈ S → -x ∈ S) →
                    (∀ x : G W C, x ∈ T → -x ∈ T) →
                      sourceThreePeriodic S →
                        ∀ (π : C ≃ C),
                          π 0 = 0 →
                            ∀ (a : C → W) (b : C → C9) (k : C → ZMod 3),
                              a 0 = 0 →
                                b 0 = 0 →
                                  k 0 = 0 →
                                    (∃ c d : C, k c ≠ k d) →
                                      ∀ (f : G W C ≃ G W C),
                                        pointedStandardC9FibreIsomorphism
                                            S T f →
                                          affineTwistForm M π a b k f →
                                            ∃ L : V W C ≃ₗ[ZMod 2] V W C,
                                              ∃ u : C9ˣ,
                                                sectionTransport S T L u ∧
                                                  Set.image
                                                      (productTransport L u) S = T

end
end MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Rank5AffineTwist61380
