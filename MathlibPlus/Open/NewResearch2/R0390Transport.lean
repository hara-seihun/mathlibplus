import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

namespace MathlibPlus.Open.NewResearch2.R0390Transport

noncomputable section

/-- Claim 20806: in the explicit 61-element closure lattice, the target
coordinate 3 is outside the three tight coordinates, and its transported
join-irreducible fiber is exactly the target singleton at every proper tight
subset. -/
def claim20806 : Prop :=
  let coordMask : ℕ → ℕ := fun i => 2 ^ i
  let tightCoordinates : Finset ℕ := {0, 1, 2}
  let targetCoordinate : ℕ := 3
  let targetMask : ℕ := coordMask targetCoordinate
  let lowerCoverMask : ℕ := 0
  let joinIrreduciblesBelow : ℕ → Finset ℕ :=
    fun x =>
      let _ : DecidablePred
          (fun a : ℕ =>
            MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below a x) :=
        Classical.decPred _
      MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinIrreducibleMasks.filter
        (fun a =>
          MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below a x)
  let edgeProfile : Finset ℕ → Finset ℕ :=
    fun S =>
      joinIrreduciblesBelow
          (MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinOf
            (insert targetMask (S.image coordMask))) \
        joinIrreduciblesBelow
          (MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinOf
            (insert lowerCoverMask (S.image coordMask)))
  targetCoordinate ∉ tightCoordinates ∧
    ∀ S : Finset ℕ, S ⊂ tightCoordinates →
      edgeProfile S = {targetMask}

end

end MathlibPlus.Open.NewResearch2.R0390Transport
