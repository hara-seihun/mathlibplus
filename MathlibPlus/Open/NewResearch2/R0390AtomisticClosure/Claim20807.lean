import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

namespace MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

noncomputable section

/-- The mask obtained by joining a finite family of coordinate masks. -/
def coordinateMask (S : Finset ℕ) : ℕ :=
  S.toList.foldl Nat.lor 0

/-- The lower-cover relation in the displayed closure lattice. -/
def closureLowerCover (jStar j : ℕ) : Prop :=
  jStar ∈ closureLattice ∧
    j ∈ closureLattice ∧
      jStar ≠ j ∧
        below jStar j ∧
          ∀ x ∈ closureLattice,
            below jStar x → below x j → x = jStar ∨ x = j

/-- The transport profile E_j(S) using the verified singleton
join-irreducible carrier of the 61-element closure lattice. -/
def closureTransport (jStar j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  singletonMasksBelow (joinMask j (joinOf S)) \
    singletonMasksBelow (joinMask jStar (joinOf S))

/-- At the full three-coordinate tight cube, closure reaches the top together
with the outside coordinate, while the lower-cover transport is empty. -/
def claim20807 : Prop :=
  let T : Finset ℕ := {1, 2, 4}
  let j : ℕ := 8
  let jStar : ℕ := 0
  closureLowerCover jStar j ∧
    T.card = 3 ∧
      T ⊆ singletonMasks ∧
        j ∈ singletonMasks ∧
          j ∉ T ∧
            joinOf T = coordinateMask (insert j T) ∧
              joinOf (insert j T) = coordinateMask (insert j T) ∧
                closureTransport jStar j T = ∅

end

end MathlibPlus.Open.NewResearch2.R0390AtomisticClosure
