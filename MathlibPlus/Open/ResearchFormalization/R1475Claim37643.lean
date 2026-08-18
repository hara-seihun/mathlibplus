import Mathlib
import MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight

namespace MathlibPlus.Open.ResearchFormalization.R1475Claim37643

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

/-- The block kernel of the generated pair. -/
def blockKernelSet {q : ℕ}
    (X : Subgroup (Equiv.Perm (EPoint q))) : Set (Equiv.Perm (EPoint q)) :=
  {g | g ∈ X ∧ ∀ x : ZMod q, ∀ j : Block,
    (g (x, j)).2 = j}

/-- The additive translation rows carried by the block kernel. -/
def translationProfiles {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q))) : Set (TranslationProfile q) :=
  {s | ∃ g : Equiv.Perm (EPoint q), g ∈ K ∧
    ∀ x : ZMod q, ∀ j : Block,
      g (x, j) = (x + s j, j)}

/-- The cyclic shift convention on the eight outer coordinates. -/
def translationShift {q : ℕ}
    (s : TranslationProfile q) (k : Block) : TranslationProfile q :=
  fun j => s (phaseAdd k j)

def translationProfileOf {q : ℕ}
    (m : Multiplier q) : TranslationProfile q :=
  fun j => (m j : ZMod q)

def inverseMultiplierProfile {q : ℕ}
    (m : Multiplier q) : Multiplier q :=
  fun j => (m j)⁻¹

def oneTranslationProfile {q : ℕ} : TranslationProfile q :=
  fun _ => 1

/-- Periodicity under the separation of two outer blocks. -/
def periodicSeparation {q : ℕ}
    (h : Multiplier q) (i j : Block) : Prop :=
  ∀ k : Block, h (phaseAdd k i) = h (phaseAdd k j)

/-- The determinant of the all-ones row and an additive slope row after
restriction to the selected two blocks. -/
def rowDeterminant {q : ℕ}
    (s : TranslationProfile q) (i j : Block) : ZMod q :=
  s i - s j

/-- Restriction/projection of the block-kernel translation rows to a pair is
surjective.  No zero condition is imposed on the other six coordinates. -/
def fullPairTranslationProjection {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q))) (i j : Block) : Prop :=
  ∀ u v : ZMod q, ∃ s : TranslationProfile q,
    s ∈ translationProfiles K ∧ s i = u ∧ s j = v

/-- The translation plane supplies a transporter for arbitrary points on the
selected two blocks, without putting the normalized chart itself in `X`. -/
def translatesPairToNormalizedImage {q : ℕ}
    (K : Set (Equiv.Perm (EPoint q)))
    (h : Multiplier q) (i j : Block) : Prop :=
  ∀ x y : ZMod q, ∃ s : TranslationProfile q,
    s ∈ translationProfiles K ∧
      s i = (h i : ZMod q) * x - x ∧
      s j = (h j : ZMod q) * y - y

/-- Claim 37643: an aperiodic separation has a shifted translation row with
nonzero determinant against the all-ones row, and its pair projection and
point-pair action are full. -/
def claim37643_nonperiodFullTranslationPlane : Prop :=
  ∀ q : ℕ, (Nat.Prime q ∧ Odd q) →
    ∀ a : Multiplier q,
      ∀ R : Subgroup (Equiv.Perm (EPoint q)),
        sourceRegularCopy q R →
          ∀ F : Equiv.Perm (EPoint q),
            pureMultiplierFormula a F →
              let h := fun j => a j / a 0
              let X := generatedPair R F
              let K := blockKernelSet X
              ∀ i j : Block, i ≠ j →
                ¬ periodicSeparation h i j →
                  oneTranslationProfile ∈ translationProfiles K ∧
                    (∃ s : TranslationProfile q, ∃ k : Block,
                      (s =
                          translationShift (translationProfileOf h) k ∨
                        s = translationShift
                          (translationProfileOf
                            (inverseMultiplierProfile h)) k) ∧
                      s ∈ translationProfiles K ∧
                      s i ≠ s j ∧
                      rowDeterminant s i j ≠ 0) ∧
                    fullPairTranslationProjection K i j ∧
                    translatesPairToNormalizedImage K h i j

end MathlibPlus.Open.ResearchFormalization.R1475Claim37643
