import Mathlib
import MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight

namespace MathlibPlus.Open.ResearchFormalization.R1475Claim37644

abbrev EPoint (q : ℕ) :=
  MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight.ECoordinate q
abbrev Block := Fin 8
abbrev Multiplier (q : ℕ) := Block → (ZMod q)ˣ

open MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight

/-- The marked source copy in the standard left-regular coordinates. -/
def sourceRegularCopy (q : ℕ)
    (R : Subgroup (Equiv.Perm (EPoint q))) : Prop :=
  (∀ r : R, ∃ y : EPoint q,
    ∀ x : EPoint q,
      (r : Equiv.Perm (EPoint q)) x = coordinateMul y x) ∧
  (∀ y : EPoint q, ∃ r : R,
    ∀ x : EPoint q,
      (r : Equiv.Perm (EPoint q)) x = coordinateMul y x) ∧
  (∀ x y : EPoint q, ∃! r : R,
    (r : Equiv.Perm (EPoint q)) x = y)

/-- The pure-multiplier chart on the eight displayed outer blocks. -/
def pureMultiplierFormula {q : ℕ}
    (a : Multiplier q) (F : Equiv.Perm (EPoint q)) : Prop :=
  ∀ x : ZMod q, ∀ j : Block,
    F (x, j) = ((a j : ZMod q) * x, j)

/-- The conjugated source copy, using `R^F = F⁻¹ R F`. -/
def conjugatedSet {q : ℕ}
    (R : Subgroup (Equiv.Perm (EPoint q))) (F : Equiv.Perm (EPoint q)) :
    Set (Equiv.Perm (EPoint q)) :=
  {u | ∃ r : R,
    u = F⁻¹ * (r : Equiv.Perm (EPoint q)) * F}

/-- The generated marked pair. -/
def generatedPair {q : ℕ}
    (R : Subgroup (Equiv.Perm (EPoint q))) (F : Equiv.Perm (EPoint q)) :
    Subgroup (Equiv.Perm (EPoint q)) :=
  Subgroup.closure ((R : Set (Equiv.Perm (EPoint q))) ∪ conjugatedSet R F)

/-- The block kernel of the generated pair. -/
def blockKernelSet {q : ℕ}
    (X : Subgroup (Equiv.Perm (EPoint q))) : Set (Equiv.Perm (EPoint q)) :=
  {g | g ∈ X ∧ ∀ x : ZMod q, ∀ j : Block,
    (g (x, j)).2 = j}

/-- Fibre-multiplier rows in the block kernel. -/
def slopeProfiles {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q))) : Set (Multiplier q) :=
  {m | ∃ g : Equiv.Perm (EPoint q), g ∈ K ∧
    ∀ x : ZMod q, ∀ j : Block,
      g (x, j) = ((m j : ZMod q) * x, j)}

def multiplierShift {q : ℕ}
    (m : Multiplier q) (k : Block) : Multiplier q :=
  fun j => m (phaseAdd k j)

/-- The adjacent multiplier-ratio word. -/
def adjacentRatio {q : ℕ} (h : Multiplier q) : Multiplier q :=
  fun j => h (phaseAdd j 1) / h j

/-- Periodicity under the separation of two outer blocks. -/
def periodicSeparation {q : ℕ}
    (h : Multiplier q) (i j : Block) : Prop :=
  ∀ k : Block, h (phaseAdd k i) = h (phaseAdd k j)

/-- The product of the shifted adjacent-ratio rows used by the telescoping
construction.  Its shifts are indexed so that their values at `i` are the
successive ratios from block zero up to block `i`. -/
def shiftedRatioProduct {q : ℕ}
    (h : Multiplier q) (i : Block) : Multiplier q :=
  ∏ k ∈ Finset.Iio i,
    multiplierShift (adjacentRatio h) (k - i)

/-- The pairwise slope action at arbitrary points. -/
def slopePairTransport {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q)))
    (h : Multiplier q) (i j : Block) : Prop :=
  ∀ x y : ZMod q, ∃ g : Equiv.Perm (EPoint q), g ∈ K ∧
    g (x, i) = ((h i : ZMod q) * x, i) ∧
    g (y, j) = ((h j : ZMod q) * y, j)

/-- Two arbitrary points in one outer block are transported by the same
normalized local slope. -/
def slopeSameBlockTransport {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q)))
    (h : Multiplier q) (i : Block) : Prop :=
  ∀ x y : ZMod q, ∃ g : Equiv.Perm (EPoint q), g ∈ K ∧
    g (x, i) = ((h i : ZMod q) * x, i) ∧
    g (y, i) = ((h i : ZMod q) * y, i)

/-- Claim 37644: on a periodic pair, adjacent-ratio slope rows are diagonal,
and their shifted product supplies the normalized slope on both blocks. -/
def claim37644_periodDiagonalTelescoping : Prop :=
  ∀ q : ℕ, (Nat.Prime q ∧ Odd q) →
    ∀ a : Multiplier q,
      ∀ R : Subgroup (Equiv.Perm (EPoint q)),
        sourceRegularCopy q R →
          ∀ F : Equiv.Perm (EPoint q),
            pureMultiplierFormula a F →
              let h := fun j => a j / a 0
              let X := generatedPair R F
              let K := blockKernelSet X
              h 0 = 1 ∧
                ∀ i j : Block, periodicSeparation h i j →
                  h i = h j ∧
                    (∀ k : Block,
                      multiplierShift (adjacentRatio h) k ∈ slopeProfiles K ∧
                        (multiplierShift (adjacentRatio h) k) i =
                          (multiplierShift (adjacentRatio h) k) j) ∧
                    shiftedRatioProduct h i ∈ slopeProfiles K ∧
                    (shiftedRatioProduct h i) i = h i ∧
                    (shiftedRatioProduct h i) j = h i ∧
                    slopePairTransport K h i j ∧
                    slopeSameBlockTransport K h i ∧
                    slopeSameBlockTransport K h j

end MathlibPlus.Open.ResearchFormalization.R1475Claim37644
