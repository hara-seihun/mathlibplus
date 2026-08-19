import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61266NonsplitCosetSwitch

noncomputable section

/-- The index-two condition for a subgroup of a finite additive abelian group. -/
def indexTwoAddSubgroup {G : Type*} [AddCommGroup G] [Fintype G]
    (K : AddSubgroup G) : Prop :=
  letI : Fintype K := Fintype.ofFinite K
  Fintype.card G = 2 * Fintype.card K

/-- The elementary-abelian Sylow-two hypothesis on the subgroup. -/
def elementarySylowTwo {G : Type*} [AddCommGroup G] [Fintype G]
    (K : AddSubgroup G) : Prop :=
  letI : Fintype K := Fintype.ofFinite K
  ∃ P : Sylow 2 (Multiplicative K), ∀ x : P, x ^ 2 = 1

/-- Identity-free inverse-closed connection sets in additive notation. -/
def identityFreeInverseClosed {G : Type*} [AddCommGroup G]
    (S : Set G) : Prop :=
  0 ∉ S ∧ ∀ x : G, x ∈ S → -x ∈ S

/-- The given permutation as an ordinary undirected Cayley-graph
isomorphism. -/
def ordinaryAdditiveCayleyIso {G : Type*} [AddCommGroup G]
    (S T : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G,
    (SimpleGraph.addCayley S).Adj x y ↔
      (SimpleGraph.addCayley T).Adj (f x) (f y)

/-- The displayed map on the two cosets, with the subgroup fixed pointwise. -/
def cosetSwitchFormula {G : Type*} [AddCommGroup G]
    (K : AddSubgroup G) (a : G) (φ : Equiv.Perm K) (f : Equiv.Perm G) : Prop :=
  (∀ k : K, f (k : G) = (k : G)) ∧
    (∀ k : K, f (a + (k : G)) = a + (φ k : G))

/-- The common group-automorphism shadow, including both displayed coset
formulas. -/
def commonAutomorphismFormula {G : Type*} [AddCommGroup G]
    (K : AddSubgroup G) (a e : G) (α : G ≃+ G) : Prop :=
  ∀ k : K,
    α (k : G) = (k : G) ∧
      α (a + (k : G)) = a + e + (k : G)

/-- The simultaneous finite-tuple conclusion for a fixed index-two subgroup. -/
def cosetSwitchShadowFor {G : Type*} [AddCommGroup G] [Fintype G]
    (K : AddSubgroup G) : Prop :=
  indexTwoAddSubgroup K →
    elementarySylowTwo K →
      ∀ (a : G), a ∉ (K : Set G) →
        ∀ (φ : Equiv.Perm K) (f : Equiv.Perm G),
          cosetSwitchFormula K a φ f →
            ∀ (I : Type) [Fintype I] (S T : I → Set G),
              (∀ i : I,
                identityFreeInverseClosed (S i) ∧
                  identityFreeInverseClosed (T i)) →
              (∀ i : I, ordinaryAdditiveCayleyIso (S i) (T i) f) →
              ∃ e : G,
                e ∈ (K : Set G) ∧
                  2 • e = 0 ∧
                    ∃ α : G ≃+ G,
                      commonAutomorphismFormula K a e α ∧
                        ∀ i : I,
                          Set.image (fun x => α x) (S i) = T i

/-- The finite elementary-abelian two-group condition used in the cyclic-four
specialization. -/
def elementaryTwoAdditiveGroup (E : Type*) [AddCommGroup E] : Prop :=
  ∀ x : E, 2 • x = 0

/-- The even half-layer in `C₄ × E × O`; its first coordinate is `2 C₄` and
the other coordinates are unrestricted. -/
def c4EvenHalfLayer (E O : Type*) : Set (ZMod 4 × (E × O)) :=
  {x | ∃ c : ZMod 4, x.1 = 2 • c}

/-- The cyclic-four nonsplit specialization and its arbitrary finite carried
tuple of ordinary Cayley relations. -/
def c4NonsplitApplication : Prop :=
  ∀ (E O : Type) [AddCommGroup E] [Fintype E]
    [AddCommGroup O] [Fintype O],
    elementaryTwoAdditiveGroup E →
      Odd (Fintype.card O) →
        ∃ K : AddSubgroup (ZMod 4 × (E × O)),
          (K : Set (ZMod 4 × (E × O))) = c4EvenHalfLayer E O ∧
            indexTwoAddSubgroup K ∧
              elementarySylowTwo K ∧
                cosetSwitchShadowFor K

/--
Claim 61266: an arbitrary permutation of the nontrivial coset, fixing the
index-two subgroup pointwise, cannot produce a simultaneous ordinary Cayley
shadow not already carried by one common automorphism; the same element of
`K[2]` works for every finite label tuple.  The cyclic-four half-layer
specialization is included explicitly.
-/
def claim61266 : Prop :=
  (∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (K : AddSubgroup G),
      cosetSwitchShadowFor K) ∧
    c4NonsplitApplication

end

end MathlibPlus.Open.ResearchFormalization.Claim61266NonsplitCosetSwitch
