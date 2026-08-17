import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch55340_55341

/-- The left coset of `U` represented by `x`, as a point of `R/U`. -/
noncomputable def cosetPoint {R : Type*} [Group R]
    (U : Subgroup R) (x : R) : R ⧸ U :=
  QuotientGroup.mk x

/-- The double coset `UxU`. -/
def doubleCoset {R : Type*} [Group R]
    (U : Subgroup R) (x : R) : Set R :=
  {y | ∃ u : U, ∃ v : U, y = (u : R) * x * (v : R)}

/-- The `U`-orbit of the point `xU` in the left-coset space `R/U`. -/
noncomputable def uCosetOrbit {R : Type*} [Group R] [Fintype R]
    (U : Subgroup R) (x : R) : Set (R ⧸ U) :=
  MulAction.orbit U (cosetPoint U x)

/-- The diagonal orbital through `(U,xU)` in `(R/U)²`. -/
noncomputable def diagonalOrbital {R : Type*} [Group R] [Fintype R]
    (U : Subgroup R) (x : R) : Set ((R ⧸ U) × (R ⧸ U)) :=
  MulAction.orbit R (cosetPoint U (1 : R), cosetPoint U x)

/-- The subdegree multiset indexed by the distinct `U`-orbits on `R/U`. -/
noncomputable def orbitSubdegreeMultiset {R : Type*} [Group R] [Fintype R]
    (U : Subgroup R) : Multiset ℕ := by
  classical
  exact
    (Finset.univ.image (fun x : R =>
      (uCosetOrbit U x, Set.ncard (uCosetOrbit U x)))).1.map Prod.snd

/-- The multiset of relative indices indexed by the distinct double cosets. -/
noncomputable def doubleCosetSubdegreeMultiset {R : Type*} [Group R] [Fintype R]
    (U : Subgroup R) : Multiset ℕ := by
  classical
  exact
    (Finset.univ.image (fun x : R =>
      (doubleCoset U x,
        (U ⊓ Subgroup.map (MulAut.conj x).toMonoidHom U).relIndex U))).1.map Prod.snd

/-- The double-coset indexing and complete subdegree multiset formula. -/
def claim55340 {R : Type*} [Group R] [Fintype R]
    (U : Subgroup R) : Prop :=
  (∀ x y : R,
    uCosetOrbit U x = uCosetOrbit U y ↔ doubleCoset U x = doubleCoset U y) ∧
    (∀ x : R,
      Set.ncard (uCosetOrbit U x) =
        (U ⊓ Subgroup.map (MulAut.conj x).toMonoidHom U).relIndex U) ∧
    orbitSubdegreeMultiset U = doubleCosetSubdegreeMultiset U

/-- The orbital-size formula and disjointness for distinct double cosets. -/
def claim55341 {R : Type*} [Group R] [Fintype R]
    (U : Subgroup R) : Prop :=
  (∀ x : R,
    Set.ncard (diagonalOrbital U x) =
      U.index * (U ⊓ Subgroup.map (MulAut.conj x).toMonoidHom U).relIndex U) ∧
    (∀ x y : R,
      doubleCoset U x ≠ doubleCoset U y →
        Disjoint (diagonalOrbital U x) (diagonalOrbital U y))

end MathlibPlus.Open.ResearchFormalizationBatch55340_55341
