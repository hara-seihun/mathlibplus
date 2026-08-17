import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim37231

noncomputable section

private abbrev F7 := ZMod 7
private abbrev F3 := ZMod 3
private abbrev H := F7 × F3
private abbrev W := F7 × F7
private abbrev G := W × H

private def hOne : H := (0, 0)

private def hMul (h k : H) : H :=
  (h.1 + (2 : F7) ^ h.2.val * k.1, h.2 + k.2)

private def hInv (h : H) : H :=
  (-(2 : F7) ^ (-h.2).val * h.1, -h.2)

private def hScalar (h : H) (w : W) : W :=
  ((2 : F7) ^ h.2.val * w.1,
    (2 : F7) ^ h.2.val * w.2)

private def gOne : G := ((0, 0), hOne)

private def gMul (x y : G) : G :=
  (x.1 + hScalar x.2 y.1, hMul x.2 y.2)

private def gInv (x : G) : G :=
  (hScalar (hInv x.2) (-x.1), hInv x.2)

private def normalizedFunction (τ : H → W) : Prop :=
  τ hOne = 0

private def normalizedCocycle (z : H → W) : Prop :=
  z hOne = 0 ∧
    ∀ h k : H, z (hMul h k) = z h + hScalar h (z k)

private def derivativeSubspace (τ : H → W) (h : H) : Submodule F7 W :=
  Submodule.span F7
    {d : W | ∃ k : H,
      d = τ (hMul h k) - τ h - hScalar h (τ k)}

private def affineCoset (D : Submodule F7 W) (w : W) : Set W :=
  {u | ∃ d : W, d ∈ D ∧ u = w + d}

private def relativeDerivativeOrbit (τ : H → W) (h : H) (w : W) : Set G :=
  {x | x.2 = h ∧ x.1 ∈ affineCoset (derivativeSubspace τ h) w}

private def pureTranslationProfile (τ : H → W) : G → G :=
  fun x => (x.1 + τ x.2, x.2)

private def cocycleAutomorphismShadow (z : H → W) : G → G :=
  fun x => (x.1 + z x.2, x.2)

private def groupLikeAutomorphism (α : G → G) : Prop :=
  Function.Bijective α ∧
    α gOne = gOne ∧
      ∀ x y : G, α (gMul x y) = gMul (α x) (α y)

private def sameCosetTranslationImage (τ z : H → W) : Prop :=
  ∀ h : H, ∀ w : W,
    Set.image (fun u : W => u + τ h)
        (affineCoset (derivativeSubspace τ h) w) =
      Set.image (fun u : W => u + z h)
        (affineCoset (derivativeSubspace τ h) w)

private def orbitImageAgreement (τ z : H → W) : Prop :=
  ∀ h : H, ∀ w : W,
    Set.image (pureTranslationProfile τ)
        (relativeDerivativeOrbit τ h w) =
      Set.image (cocycleAutomorphismShadow z)
        (relativeDerivativeOrbit τ h w)

private def profileConnectionSet (τ : H → W) (S : Set G) : Prop :=
  ∀ x : G, x ∈ S →
    ∃ h : H, ∃ w : W,
      x ∈ relativeDerivativeOrbit τ h w ∧
        relativeDerivativeOrbit τ h w ⊆ S

private def inverseClosedProfileSet (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ gInv x ∈ S

private def profileDCIHarmless (τ z : H → W) : Prop :=
  ∀ S : Set G, profileConnectionSet τ S →
    Set.image (pureTranslationProfile τ) S =
      Set.image (cocycleAutomorphismShadow z) S

private def profileCIHarmless (τ z : H → W) : Prop :=
  ∀ S : Set G, profileConnectionSet τ S →
    inverseClosedProfileSet S →
      Set.image (pureTranslationProfile τ) S =
        Set.image (cocycleAutomorphismShadow z) S

private def hGroupLaw : Prop :=
  (∀ x y z : H, hMul (hMul x y) z = hMul x (hMul y z)) ∧
    (∀ x : H, hMul hOne x = x ∧ hMul x hOne = x) ∧
      (∀ x : H,
        hMul x (hInv x) = hOne ∧ hMul (hInv x) x = hOne)

private def gGroupLaw : Prop :=
  (∀ x y z : G, gMul (gMul x y) z = gMul x (gMul y z)) ∧
    (∀ x : G, gMul gOne x = x ∧ gMul x gOne = x) ∧
      (∀ x : G,
        gMul x (gInv x) = gOne ∧ gMul (gInv x) x = gOne)

/-- The Record-10 cocycle shadow agrees with every pure-translation profile
on the exact derivative orbits and on every directed admitted connection
set, with the inverse-closed CI case as a specialization. -/
def claim37231 : Prop :=
  hGroupLaw ∧
    gGroupLaw ∧
      ∀ τ : H → W, normalizedFunction τ →
        ∃ z : H → W,
          normalizedCocycle z ∧
            (∀ h : H,
              τ h - z h ∈ derivativeSubspace τ h) ∧
            sameCosetTranslationImage τ z ∧
              groupLikeAutomorphism (cocycleAutomorphismShadow z) ∧
                orbitImageAgreement τ z ∧
                  profileDCIHarmless τ z ∧
                    profileCIHarmless τ z

end

end MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim37231
