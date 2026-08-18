import MathlibPlus.Open.ResearchBatch.AdvancedGroups

namespace MathlibPlus.Open.ResearchFormalization.R1591

noncomputable section

open MathlibPlus.Open.ResearchBatch.AdvancedGroups

private def affineOrbitFamily {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    (Γ : Subgroup (Equiv.Perm W)) : Set (Set W) :=
  Set.range (affineOrbit Γ)

private def translatedOrbit {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    (v : W) (O : Set W) : Set W :=
  Set.image (affineMap v (1 : W ≃ₗ[K] W)) O

private def commonOrbitTranslationStabilizer {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    (Γ : Subgroup (Equiv.Perm W)) : Set W :=
  {v | ∀ O : Set W, O ∈ affineOrbitFamily (K := K) Γ →
    translatedOrbit (K := K) v O = O}

private def translationCore {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    (Γ : Subgroup (Equiv.Perm W)) : Set W :=
  {v | affineMap v (1 : W ≃ₗ[K] W) ∈ Γ}

private def translationCoreCoset {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    (Γ : Subgroup (Equiv.Perm W)) (x : W) : Set W :=
  {y | ∃ v ∈ translationCore (K := K) Γ,
    affineMap v (1 : W ≃ₗ[K] W) x = y}

/-- Claim 39439: on a finite-dimensional vector space and a genuine affine
subgroup, the common orbit-translation stabilizer and translation core are
exactly the two displayed sets, with no arbitrary replacement sets. -/
def claim39439_commonAffineOrbitTranslationStabilizer : Prop :=
  ∀ {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Fintype W]
    (C : Subgroup (W ≃ₗ[K] W))
    (Γ : Subgroup (Equiv.Perm W)),
    affineContainedIn C Γ →
      let T : Set W := commonOrbitTranslationStabilizer (K := K) Γ
      let V : Set W := translationCore (K := K) Γ
      (∀ δ : W, δ ∈ T ↔
        ∀ O : Set W, O ∈ affineOrbitFamily (K := K) Γ →
          translatedOrbit (K := K) δ O = O) ∧
        (∀ δ : W, δ ∈ V ↔
          affineMap δ (1 : W ≃ₗ[K] W) ∈ Γ)

/-- Claim 39441: every translation in the affine translation core preserves
all affine orbits, without a p-prime or linear-image hypothesis. -/
def claim39441_coreTranslationsPreserveEveryOrbit : Prop :=
  ∀ {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Fintype W]
    (C : Subgroup (W ≃ₗ[K] W))
    (Γ : Subgroup (Equiv.Perm W)),
    affineContainedIn C Γ →
      translationCore (K := K) Γ ⊆ commonOrbitTranslationStabilizer (K := K) Γ

/-- Claim 39445: if one affine orbit is exactly the coset of the translation
core through a point, every common orbit-translation stabilizer element lies
in that core. -/
def claim39445_coreCosetForcesReverseInclusion : Prop :=
  ∀ {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Fintype W]
    (C : Subgroup (W ≃ₗ[K] W))
    (Γ : Subgroup (Equiv.Perm W)) (x : W),
    affineContainedIn C Γ →
      affineOrbit Γ x = translationCoreCoset (K := K) Γ x →
        commonOrbitTranslationStabilizer (K := K) Γ ⊆ translationCore (K := K) Γ

end

end MathlibPlus.Open.ResearchFormalization.R1591
