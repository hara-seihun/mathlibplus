import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1441Claim37234

noncomputable section

private abbrev F7 := ZMod 7
private abbrev F3 := ZMod 3
private abbrev H := F7 × F3
private abbrev W := F7 × F7

private def hOne : H := (0, 0)

private def hMul (h k : H) : H :=
  (h.1 + (2 : F7) ^ h.2.val * k.1, h.2 + k.2)

private def hScalar (h : H) (w : W) : W :=
  ((2 : F7) ^ h.2.val * w.1,
    (2 : F7) ^ h.2.val * w.2)

private def normalizedFunction (τ : H → W) : Prop :=
  τ hOne = 0

private def derivativeSubspace (τ : H → W) (h : H) : Submodule F7 W :=
  Submodule.span F7
    {d : W | ∃ k : H,
      d = τ (hMul h k) - τ h - hScalar h (τ k)}

private def affineCoset (D : Submodule F7 W) (w : W) : Set W :=
  {u | ∃ d : W, d ∈ D ∧ u = w + d}

private def derivativeOrbitFamily (τ : H → W) (h : H) : Set (Set W) :=
  {O | ∃ w : W, O = affineCoset (derivativeSubspace τ h) w}

private def rowTranslation (t : W) (O : Set W) : Set W :=
  Set.image (fun w => w + t) O

private def commonOrbitPeriod (τ : H → W) (h : H) : Set W :=
  {t | ∀ O : Set W,
    O ∈ derivativeOrbitFamily τ h →
      rowTranslation t O = O}

/-- The common translation periods of the exact derivative-orbit cosets form
an `F₇`-subspace, and precisely measure equality of row-translation actions. -/
def claim37234 : Prop :=
  ∀ τ : H → W, normalizedFunction τ →
    ∀ h : H,
      ∃ T : Submodule F7 W,
        (∀ t : W,
          t ∈ T ↔ t ∈ commonOrbitPeriod τ h) ∧
          ∀ t₁ t₂ : W,
            ((∀ O : Set W,
                O ∈ derivativeOrbitFamily τ h →
                  rowTranslation t₁ O = rowTranslation t₂ O) ↔
              t₁ - t₂ ∈ T)

end

end MathlibPlus.Open.ResearchFormalization.R1441Claim37234
