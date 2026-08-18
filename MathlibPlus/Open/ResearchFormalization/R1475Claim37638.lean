import Mathlib
import MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight

namespace MathlibPlus.Open.ResearchFormalization.R1475Claim37638

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

/-- Conjugation by a global scalar preserves the marked source copy. -/
def normalizes {q : ℕ}
    (R : Subgroup (Equiv.Perm (EPoint q))) (G : Equiv.Perm (EPoint q)) : Prop :=
  ∀ u : Equiv.Perm (EPoint q),
    u ∈ R ↔ G⁻¹ * u * G ∈ R

/-- The normalized multiplier word. -/
def normalizedProfile {q : ℕ} (a : Multiplier q) : Multiplier q :=
  fun j => a j / a 0

/-- The normalized chart formula. -/
def normalizedMapFormula {q : ℕ}
    (h : Multiplier q) (H : Equiv.Perm (EPoint q)) : Prop :=
  ∀ x : ZMod q, ∀ j : Block,
    H (x, j) = ((h j : ZMod q) * x, j)

/-- The global scalar chart formula. -/
def scalarMapFormula {q : ℕ}
    (lambda : (ZMod q)ˣ) (G : Equiv.Perm (EPoint q)) : Prop :=
  ∀ x : ZMod q, ∀ j : Block,
    G (x, j) = ((lambda : ZMod q) * x, j)

/-- Claim 37638: global scalar normalization, without asserting that the
original chart belongs to the generated group or its two-closure. -/
def claim37638_globalScalarNormalization : Prop :=
  ∀ q : ℕ, (Nat.Prime q ∧ Odd q) →
    ∀ a : Multiplier q,
      ∀ R : Subgroup (Equiv.Perm (EPoint q)),
        sourceRegularCopy q R →
          ∀ F : Equiv.Perm (EPoint q),
            pureMultiplierFormula a F →
              let lambda := a 0
              let h := normalizedProfile a
              h 0 = 1 ∧
                ∃ H G : Equiv.Perm (EPoint q),
                  normalizedMapFormula h H ∧
                  scalarMapFormula lambda G ∧
                  F = G * H ∧
                  F = H * G ∧
                  normalizes R G ∧
                  conjugatedSet R F = conjugatedSet R H

end MathlibPlus.Open.ResearchFormalization.R1475Claim37638
