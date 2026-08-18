import Mathlib
import MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight

namespace MathlibPlus.Open.ResearchFormalization.R1475Claim37641

abbrev EPoint (q : ℕ) :=
  MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight.ECoordinate q
abbrev Block := Fin 8
abbrev Multiplier (q : ℕ) := Block → (ZMod q)ˣ
abbrev TranslationProfile (q : ℕ) := Block → ZMod q

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

/-- The block kernel of the generated pair: its elements fix every outer
block, while their actions on a block may be translations or multipliers. -/
def blockKernelSet {q : ℕ}
    (X : Subgroup (Equiv.Perm (EPoint q))) : Set (Equiv.Perm (EPoint q)) :=
  {g | g ∈ X ∧ ∀ x : ZMod q, ∀ j : Block,
    (g (x, j)).2 = j}

/-- Translation profiles are additive rows, not fibre multipliers. -/
def translationProfiles {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q))) : Set (TranslationProfile q) :=
  {s | ∃ g : Equiv.Perm (EPoint q), g ∈ K ∧
    ∀ x : ZMod q, ∀ j : Block,
      g (x, j) = (x + s j, j)}

/-- Slope profiles are the fibre-multiplier rows. -/
def slopeProfiles {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q))) : Set (Multiplier q) :=
  {m | ∃ g : Equiv.Perm (EPoint q), g ∈ K ∧
    ∀ x : ZMod q, ∀ j : Block,
      g (x, j) = ((m j : ZMod q) * x, j)}

/-- The cyclic shift convention on the eight outer coordinates. -/
def translationShift {q : ℕ}
    (s : TranslationProfile q) (k : Block) : TranslationProfile q :=
  fun j => s (phaseAdd k j)

def multiplierShift {q : ℕ}
    (m : Multiplier q) (k : Block) : Multiplier q :=
  fun j => m (phaseAdd k j)

def translationProfileOf {q : ℕ}
    (m : Multiplier q) : TranslationProfile q :=
  fun j => (m j : ZMod q)

def oneTranslationProfile {q : ℕ} : TranslationProfile q :=
  fun _ => 1

def inverseMultiplierProfile {q : ℕ}
    (m : Multiplier q) : Multiplier q :=
  fun j => (m j)⁻¹

/-- The adjacent multiplier-ratio word. -/
def adjacentRatio {q : ℕ} (h : Multiplier q) : Multiplier q :=
  fun j => h (phaseAdd j 1) / h j

/-- Claim 37641: the three kinds of displayed rows have their actual
block-kernel carriers.  The normalized word rows are additive translations;
the adjacent-ratio rows are fibre multipliers. -/
def claim37641_generatedBlockKernelProfiles : Prop :=
  ∀ q : ℕ, (Nat.Prime q ∧ Odd q) →
    ∀ a : Multiplier q,
      ∀ R : Subgroup (Equiv.Perm (EPoint q)),
        sourceRegularCopy q R →
          ∀ F : Equiv.Perm (EPoint q),
            pureMultiplierFormula a F →
              let h := fun j => a j / a 0
              let X := generatedPair R F
              let K := blockKernelSet X
              oneTranslationProfile ∈ translationProfiles K ∧
                (∀ k : Block,
                  translationShift (translationProfileOf h) k ∈
                      translationProfiles K ∧
                    translationShift
                        (translationProfileOf (inverseMultiplierProfile h)) k ∈
                      translationProfiles K) ∧
                (∀ k : Block,
                  multiplierShift (adjacentRatio h) k ∈ slopeProfiles K ∧
                    multiplierShift
                        (inverseMultiplierProfile (adjacentRatio h)) k ∈
                      slopeProfiles K)

end MathlibPlus.Open.ResearchFormalization.R1475Claim37641
