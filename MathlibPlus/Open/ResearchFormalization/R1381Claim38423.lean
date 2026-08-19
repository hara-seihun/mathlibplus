import MathlibPlus.Open.ResearchFormalization.R1381PrimitiveAffineCounterexample

namespace MathlibPlus.Open.ResearchFormalization.R1381Claim38423

open MathlibPlus.Open.RepresentationTheory.R1381
open MathlibPlus.Open.Research.R1661
open MathlibPlus.Open.ResearchFormalization.R1381PrimitiveAffineCounterexample

noncomputable section

abbrev Q8 := QuaternionGroup 2
abbrev Plane (p : ℕ) := Fin 2 → ZMod p
abbrev GL2 (p : ℕ) := Matrix.GeneralLinearGroup (Fin 2) (ZMod p)
abbrev ProductGroup (p : ℕ) := Multiplicative (Plane p) × Q8

private def invariantProjectiveLine {p : ℕ} [NeZero p]
    (ρ : Q8 →* GL2 p) (W : Submodule (ZMod p) (Plane p)) : Prop :=
  Module.finrank (ZMod p) W = 1 ∧
    ∀ h : Q8, ∀ v : Plane p, v ∈ W → rhoAction ρ h v ∈ W

private def linePartitionFromSubmodule {p : ℕ} [NeZero p]
    (W : Submodule (ZMod p) (Plane p)) :
    Set (Set (ProductGroup p)) :=
  linePartition p W.toAddSubgroup

private def twistedLinePartitionFromSubmodule {p : ℕ} [NeZero p]
    (f : Equiv.Perm (ProductGroup p))
    (W : Submodule (ZMod p) (Plane p)) :
    Set (Set (ProductGroup p)) :=
  twistedLinePartition p f W.toAddSubgroup

def commonPrimeLineObstruction_claim38423 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ a b : ZMod p, ∃ ρ : Q8 →* GL2 p,
      q8RepresentationData p a b ρ ∧
        let R := standardRegularCopy p
        ∃ f : Equiv.Perm (ProductGroup p),
          chartPermutation ρ f ∧
            let T := twistedRegularCopy f R
            (displayedMinimumCommonFibers p R T) ∧
              (∀ W U : Submodule (ZMod p) (Plane p),
                Module.finrank (ZMod p) W = 1 →
                  Module.finrank (ZMod p) U = 1 →
                    linePartitionFromSubmodule W =
                      twistedLinePartitionFromSubmodule f U →
                      ∀ h : Q8, ∀ v : Plane p,
                        v ∈ W → rhoAction ρ h v ∈ W) ∧
                (¬ ∃ W : Submodule (ZMod p) (Plane p),
                  invariantProjectiveLine ρ W) ∧
                  ¬ commonPrimeLineRefinement p f

end

end MathlibPlus.Open.ResearchFormalization.R1381Claim38423
