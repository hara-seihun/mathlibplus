import MathlibPlus.Open.ResearchFormalizationBatch.GroupGraph

namespace MathlibPlus.Open.ResearchFormalizationBatch.R4328

open MathlibPlus.Open.ResearchFormalizationBatch.GroupGraph

noncomputable section

/-- A bijective homomorphism for the displayed `C_m ⋊ C_8` coordinate law. -/
def semidirectProductAutomorphism (m : ℕ)
    (α : GElement m → GElement m) : Prop :=
  Function.Bijective α ∧
    ∀ x y, α (semidirectProductMul m x y) =
      semidirectProductMul m (α x) (α y)

/-- The affine map on the cyclic base determined by a unit and a translation. -/
def cyclicAffineMap (m : ℕ) (u : (ZMod m)ˣ) (v : ZMod m) : ZMod m → ZMod m :=
  fun x => (u : ZMod m) * x + v

/-- The image of a Hall connection set under the common affine coordinate map. -/
def affineSetImage (m : ℕ) (u : (ZMod m)ˣ) (v : ZMod m)
    (S : Finset (ZMod m)) : Finset (ZMod m) :=
  S.image (cyclicAffineMap m u v)

/-- The coordinate map in the admitted automorphism normal form. -/
def normalFormCoordinateMap (m : ℕ) (u : (ZMod m)ˣ)
    (v : ZMod m) (k : ZMod 8) : GElement m → GElement m :=
  fun x =>
    ((u : ZMod m) * x.1 + (if x.2.val % 2 = 0 then 0 else v), k * x.2)

/-- The union of the two inverse-paired odd channel relations. -/
def twoChannelLiftedRelation (m : ℕ)
    (S₁ S₃ : Finset (ZMod m)) (x y : GElement m) : Prop :=
  liftedCayleyRelation S₁ ({1, 7} : Finset (ZMod 8)) x y ∨
    liftedCayleyRelation S₃ ({3, 5} : Finset (ZMod 8)) x y

/-- Equivalence of the two-channel lifted relations through a group automorphism. -/
def twoChannelGroupAutomorphismEquivalence (m : ℕ)
    (S₁ S₃ T₁ T₃ : Finset (ZMod m)) : Prop :=
  ∃ α : GElement m → GElement m,
    semidirectProductAutomorphism m α ∧
      ∀ x y,
        twoChannelLiftedRelation m S₁ S₃ x y ↔
          twoChannelLiftedRelation m T₁ T₃ (α x) (α y)

/-- The normal form of all automorphisms and the common affine/channel criterion. -/
def automorphismNormalFormAndChannelCriterion : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    (∀ α : GElement m → GElement m,
      semidirectProductAutomorphism m α →
        ∃ (u : (ZMod m)ˣ) (v : ZMod m) (k : ZMod 8),
          k ∈ ({1, 3, 5, 7} : Finset (ZMod 8)) ∧
            ∀ x : GElement m,
              α x = normalFormCoordinateMap m u v k x) ∧
    (∀ (S₁ S₃ T₁ T₃ : Finset (ZMod m)),
      twoChannelGroupAutomorphismEquivalence m S₁ S₃ T₁ T₃ ↔
        ∃ (u : (ZMod m)ˣ) (v : ZMod m) (k : ZMod 8),
          k ∈ ({1, 3, 5, 7} : Finset (ZMod 8)) ∧
            ((k ∈ ({1, 7} : Finset (ZMod 8)) ∧
                affineSetImage m u v S₁ = T₁ ∧
                affineSetImage m u v S₃ = T₃) ∨
              (k ∈ ({3, 5} : Finset (ZMod 8)) ∧
                affineSetImage m u v S₁ = T₃ ∧
                affineSetImage m u v S₃ = T₁)))

/-- A finite tuple of directed cyclic Cayley-relation isomorphisms. -/
def finiteTupleRelationIsomorphism {m t : ℕ}
    (f : ZMod m → ZMod m)
    (S T : Fin t → Finset (ZMod m)) : Prop :=
  ∀ j : Fin t,
    baseCayleyPresentationIsomorphism f (S j) (T j)

/-- A normalized permutation simultaneously carrying a finite relation tuple. -/
def normalizedFiniteTupleRelationIsomorphism {m t : ℕ}
    (f : ZMod m → ZMod m)
    (S T : Fin t → Finset (ZMod m)) : Prop :=
  f 0 = 0 ∧ Function.Bijective f ∧ finiteTupleRelationIsomorphism f S T

/-- The channel-preserving, zero-translation lift supplied by a common unit. -/
def zeroTranslationChannelLiftCIHarmless (m : ℕ)
    (u : (ZMod m)ˣ)
    (S₁ S₃ T₁ T₃ : Finset (ZMod m)) : Prop :=
  ∃ k : ZMod 8,
    k ∈ ({1, 7} : Finset (ZMod 8)) ∧
      semidirectProductAutomorphism m
        (normalFormCoordinateMap m u 0 k) ∧
      ∀ x y,
        twoChannelLiftedRelation m S₁ S₃ x y ↔
          twoChannelLiftedRelation m T₁ T₃
            (normalFormCoordinateMap m u 0 k x)
            (normalFormCoordinateMap m u 0 k y)

/-- Every two-channel choice from a relation tuple is a layerwise-equal lift. -/
def layerwiseEqualTupleLiftCIHarmless {m t : ℕ}
    (u : (ZMod m)ˣ)
    (S T : Fin t → Finset (ZMod m)) : Prop :=
  ∀ i j : Fin t,
    zeroTranslationChannelLiftCIHarmless m u
      (S i) (S j) (T i) (T j)

/-- The common multiplier shadow and its CI-harmless two-channel consequence. -/
def commonMultiplierShadowAndCIHarmless : Prop :=
  (∀ m : ℕ, 1 < m → Squarefree m →
    ∀ (t : ℕ)
      (S T : Fin t → Finset (ZMod m))
      (f : ZMod m → ZMod m),
      normalizedFiniteTupleRelationIsomorphism f S T →
        ∃ u : (ZMod m)ˣ,
          ∀ j : Fin t,
            affineSetImage m u 0 (S j) = T j) ∧
  (∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    ∀ (t : ℕ)
      (S T : Fin t → Finset (ZMod m))
      (f : ZMod m → ZMod m),
      normalizedFiniteTupleRelationIsomorphism f S T →
        ∃ u : (ZMod m)ˣ,
          (∀ j : Fin t,
            affineSetImage m u 0 (S j) = T j) ∧
          layerwiseEqualTupleLiftCIHarmless u S T)

end
end MathlibPlus.Open.ResearchFormalizationBatch.R4328
