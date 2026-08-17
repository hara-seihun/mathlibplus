import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

namespace MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

noncomputable section

/-- The three displayed coordinate filters in the exact 61-element closure
lattice all have the required half-plus-one size. -/
def claim20803 : Prop :=
  closureLattice.card = 61 ∧
    (1 : ℕ) ∈ singletonMasks ∧
      (2 : ℕ) ∈ singletonMasks ∧
        (4 : ℕ) ∈ singletonMasks ∧
          (closedUpperBounds 1).card = 31 ∧
            (closedUpperBounds 2).card = 31 ∧
              (closedUpperBounds 4).card = 31 ∧
                (closedUpperBounds 1).card =
                    (closureLattice.card + 1) / 2 ∧
                  (closedUpperBounds 2).card =
                    (closureLattice.card + 1) / 2 ∧
                    (closedUpperBounds 4).card =
                      (closureLattice.card + 1) / 2

end

end MathlibPlus.Open.NewResearch2.R0390AtomisticClosure
