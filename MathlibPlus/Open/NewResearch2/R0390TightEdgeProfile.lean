import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

namespace MathlibPlus.Open.NewResearch2.R0390TightEdgeProfile

open MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

noncomputable section

/-- The mask of the join-irreducible coordinate indexed by `i`. -/
def coordinateMask (i : Fin 8) : ℕ :=
  2 ^ i.val

/-- The three tight singleton masks in the displayed R-0390 lattice. -/
def tightCoordinates : Finset ℕ :=
  {1, 2, 4}

/-- The outside join-irreducible is coordinate `3`. -/
def targetJoinIrreducible : ℕ :=
  8

/-- The immediate predecessor of the outside coordinate in the displayed
closure lattice. -/
def targetLowerCover : ℕ :=
  0

/-- The concrete lower-cover relation in the finite mask lattice. -/
def closureLowerCover (jStar j : ℕ) : Prop :=
  jStar ∈ closureLattice ∧
    j ∈ closureLattice ∧
      jStar ≠ j ∧
        below jStar j ∧
          ∀ x ∈ closureLattice,
            below jStar x → below x j → x = jStar ∨ x = j

/-- Join-irreducible coordinates below a closed mask, before returning to the
mask carrier. -/
def coordinateSupport (x : ℕ) : Finset (Fin 8) :=
  let _ : DecidablePred (fun i : Fin 8 => below (coordinateMask i) x) :=
    Classical.decPred _
  Finset.univ.filter (fun i : Fin 8 => below (coordinateMask i) x)

/-- The coordinate-level edge profile transported back to the mask carrier.
The profile is computed from the two endpoint supports, rather than defined as
 the displayed set difference. -/
def coordinateTransportProfile (S : Finset ℕ) : Finset ℕ :=
  let q := joinMask targetJoinIrreducible (joinOf S)
  let p := joinMask targetLowerCover (joinOf S)
  (coordinateSupport q).filter (fun i => i ∉ coordinateSupport p) |>.image coordinateMask

/-- The actual join-irreducibles below a closed mask in the supplied finite
lattice. -/
def latticeJoinIrreduciblesBelow (x : ℕ) : Finset ℕ :=
  let _ : DecidablePred
      (fun u : ℕ => joinIrreducibleMask u ∧ below u x) := Classical.decPred _
  closureLattice.filter (fun u => joinIrreducibleMask u ∧ below u x)

/-- The concrete coordinate representation and the fact that the displayed
singleton masks are the lattice's join-irreducible coordinates. -/
def representedByJoinIrreducibleCoordinates : Prop :=
  claim20802 ∧
    (Finset.univ.image coordinateMask = singletonMasks) ∧
    (∀ x ∈ closureLattice,
      (coordinateSupport x).image coordinateMask =
        latticeJoinIrreduciblesBelow x)

/-- Claim 20800: on the displayed atomistic lattice, the outside coordinate
and its lower-cover edge have the stated tight-subset transport profile. -/
def claim20800 : Prop :=
  representedByJoinIrreducibleCoordinates ∧
    targetJoinIrreducible ∉ tightCoordinates ∧
      targetJoinIrreducible ∈ joinIrreducibleMasks ∧
        tightCoordinates ⊆ joinIrreducibleMasks ∧
          closureLowerCover targetLowerCover targetJoinIrreducible ∧
            ∀ S : Finset ℕ, S ⊆ tightCoordinates →
              coordinateTransportProfile S =
                latticeJoinIrreduciblesBelow
                    (joinMask targetJoinIrreducible (joinOf S)) \
                  latticeJoinIrreduciblesBelow
                    (joinMask targetLowerCover (joinOf S))

end

end MathlibPlus.Open.NewResearch2.R0390TightEdgeProfile
