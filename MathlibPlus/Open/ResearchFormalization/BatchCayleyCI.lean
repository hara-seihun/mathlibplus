import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

section CayleyCI

abbrev C2Part := Fin 3 → ZMod 2
abbrev C3Part := Fin 2 → ZMod 3
abbrev CayleyGroup := C2Part × C3Part

/-- The additive group specified in the admitted Cayley-graph claims. -/
instance : Fintype CayleyGroup := inferInstance

/-- Inverse-closed, loopless connection sets in `C₂³ × C₃²`. -/
def IsConnectionSet (S : Finset CayleyGroup) : Prop :=
  0 ∉ S ∧ ∀ x, x ∈ S ↔ -x ∈ S

/-- The finite family of all connection sets. -/
noncomputable def connectionSets : Finset (Finset CayleyGroup) := by
  classical
  exact Finset.univ.filter IsConnectionSet

noncomputable def connectionSetsOfValency (k : ℕ) : Finset (Finset CayleyGroup) := by
  classical
  exact connectionSets.filter (fun S => S.card = k)

/-- The two kinds of inverse atoms selected by a connection set. -/
noncomputable def singletonAtomCount (S : Finset CayleyGroup) : ℕ := by
  classical
  exact (S.filter (fun x => x ≠ 0 ∧ -x = x)).card

noncomputable def pairedAtomCount (S : Finset CayleyGroup) : ℕ := by
  classical
  exact (S.filter (fun x => x ≠ 0 ∧ -x ≠ x)).card / 2

noncomputable def atomProfileCount (singletons pairs : ℕ) : ℕ := by
  classical
  exact (connectionSetsOfValency 16).filter
    (fun S => singletonAtomCount S = singletons ∧ pairedAtomCount S = pairs) |>.card

/-- Exact atom-profile census for the valency-16 connection sets. -/
def claim37084 : Prop :=
  atomProfileCount 0 8 = 10518300 ∧
  atomProfileCount 2 7 = 70682976 ∧
  atomProfileCount 4 6 = 31716720 ∧
  atomProfileCount 6 5 = 1409632 ∧
  (connectionSetsOfValency 16).card = 114327628 ∧
  (connectionSetsOfValency 16).card =
    atomProfileCount 0 8 + atomProfileCount 2 7 +
      atomProfileCount 4 6 + atomProfileCount 6 5

/-- Adjacency in the undirected Cayley graph attached to a connection set. -/
def cayleyAdj (S : Finset CayleyGroup) (x y : CayleyGroup) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Ordinary graph isomorphism between two Cayley graphs, written directly as a
bijection of the common vertex set preserving adjacency. -/
def graphIso (S T : Finset CayleyGroup) : Prop :=
  ∃ e : CayleyGroup ≃ CayleyGroup,
    ∀ x y, cayleyAdj S x y ↔ cayleyAdj T (e x) (e y)

/-- Equivalence of presentations under an automorphism of the underlying group. -/
def autEquivalent (S T : Finset CayleyGroup) : Prop :=
  ∃ e : CayleyGroup ≃+ CayleyGroup, ∀ x, x ∈ S ↔ e x ∈ T

/-- The CI property for one loopless inverse-closed Cayley presentation. -/
def isCayleyCI (S : Finset CayleyGroup) : Prop :=
  ∀ T, IsConnectionSet T → T.card = S.card → graphIso S T → autEquivalent S T

/-- All valency-`k` presentations have one presentation orbit in each ordinary
isomorphism class. -/
def oneOrbitPerGraphClass (k : ℕ) : Prop :=
  ∀ S, IsConnectionSet S → S.card = k → isCayleyCI S

abbrev Valency16ConnectionSet :=
  {S : Finset CayleyGroup // IsConnectionSet S ∧ S.card = 16}

/-- The graph-isomorphism setoid on the actual valency-16 presentations. -/
noncomputable def graphIsoSetoid : Setoid Valency16ConnectionSet where
  r S T := graphIso S.1 T.1
  iseqv := by
    constructor
    · intro S
      exact ⟨Equiv.refl _, by simp [cayleyAdj]⟩
    · intro S T h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      simpa using (h (e.symm x) (e.symm y)).symm
    · intro S T U hST hTU
      rcases hST with ⟨e, hST⟩
      rcases hTU with ⟨f, hTU⟩
      refine ⟨e.trans f, ?_⟩
      intro x y
      simpa using (hST x y).trans (hTU (e x) (e y))

/-- The cardinality of the quotient of the explicitly enumerated presentations
by ordinary graph isomorphism. -/
noncomputable instance quotientGraphClassFintype : Fintype (Quotient graphIsoSetoid) :=
  Fintype.ofFinite _

noncomputable def ordinaryGraphClassCount : ℕ :=
  Fintype.card (Quotient graphIsoSetoid)

/-- The exact singleton-fiber statement for the valency-16 graph labels. -/
def claim37091 : Prop :=
  ordinaryGraphClassCount = 37897 ∧
    ∀ S T : Valency16ConnectionSet,
      graphIso S.1 T.1 ↔ autEquivalent S.1 T.1

/-- The valency-16 CI theorem. -/
def claim37093 : Prop :=
  oneOrbitPerGraphClass 16

/-- Complement in the 71 nonzero elements of the group. -/
noncomputable def cayleyComplement (S : Finset CayleyGroup) : Finset CayleyGroup := by
  classical
  exact (Finset.univ.erase 0) \ S

/-- The complement comparison, including its action on valency, graph
isomorphism, presentation-orbit equivalence, and the one-orbit property. -/
def claim37097 : Prop :=
  (∀ S, IsConnectionSet S →
    IsConnectionSet (cayleyComplement S) ∧
      (cayleyComplement S).card = 71 - S.card) ∧
  (∀ S T, IsConnectionSet S → IsConnectionSet T →
    (graphIso S T ↔ graphIso (cayleyComplement S) (cayleyComplement T)) ∧
    (autEquivalent S T ↔
      autEquivalent (cayleyComplement S) (cayleyComplement T))) ∧
  (∀ k, oneOrbitPerGraphClass k ↔ oneOrbitPerGraphClass (71 - k))

/-- Every valency-55 presentation is CI, the complement transfer of the
valency-16 theorem. -/
def claim37099 : Prop :=
  oneOrbitPerGraphClass 55

/-- The combined exact finite CI boundary. -/
def claim37102 : Prop :=
  ∀ k, (k ≤ 16 ∨ 55 ≤ k) → oneOrbitPerGraphClass k

end CayleyCI

end

end MathlibPlus.Open.ResearchFormalization
