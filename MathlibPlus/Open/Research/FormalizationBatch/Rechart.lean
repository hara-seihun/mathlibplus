import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

/-- The canonical lift on the range of an injective linear chart. -/
noncomputable def canonicalRangeLift
    {𝕜 K Y E : Type*} [Field 𝕜]
    [AddCommGroup K] [AddCommGroup Y] [AddCommGroup E]
    [Module 𝕜 K] [Module 𝕜 Y] [Module 𝕜 E]
    (A : K →ₗ[𝕜] Y) (D : K →ₗ[𝕜] E)
    (hA : Function.Injective A) : A.range →ₗ[𝕜] E :=
  D.comp (LinearEquiv.ofInjective A hA).symm.toLinearMap

/-- A target transition sends the source-chart range into the recharted range. -/
def MapsRange
    {𝕜 K Y Y' : Type*} [Field 𝕜]
    [AddCommGroup K] [AddCommGroup Y] [AddCommGroup Y']
    [Module 𝕜 K] [Module 𝕜 Y] [Module 𝕜 Y']
    (A : K →ₗ[𝕜] Y) (A' : K →ₗ[𝕜] Y') (β : Y →ₗ[𝕜] Y') : Prop :=
  ∀ y, y ∈ A.range → β y ∈ A'.range

/-- Claim 43318: genuine rechart commutation carries the chart range and its
canonical lift to the recharted range. -/
def canonicalRangeLiftRechartNaturality : Prop :=
  ∀ (𝕜 K Y Y' E : Type*)
    [Field 𝕜]
    [AddCommGroup K] [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup E]
    [Module 𝕜 K] [Module 𝕜 Y] [Module 𝕜 Y'] [Module 𝕜 E]
    (A : K →ₗ[𝕜] Y) (A' : K →ₗ[𝕜] Y')
    (α : K →ₗ[𝕜] K) (β : Y →ₗ[𝕜] Y')
    (D D' : K →ₗ[𝕜] E),
    (hA : Function.Injective A) →
    (hA' : Function.Injective A') →
    Function.Bijective α →
    A'.comp α = β.comp A →
    D'.comp α = D →
    MapsRange A A' β ∧
      ∀ (hβ : MapsRange A A' β) (y : A.range),
        canonicalRangeLift A' D' hA'
          ⟨β y, hβ y y.property⟩ =
        canonicalRangeLift A D hA y

/-- The lift associated with a local chart and its explicit embedding into a
fixed global coordinate space. -/
noncomputable def canonicalEmbeddedLift
    {𝕜 K Y V E : Type*} [Field 𝕜]
    [AddCommGroup K] [AddCommGroup Y] [AddCommGroup V] [AddCommGroup E]
    [Module 𝕜 K] [Module 𝕜 Y] [Module 𝕜 V] [Module 𝕜 E]
    (A : K →ₗ[𝕜] Y) (i : K →ₗ[𝕜] V) (D : V →ₗ[𝕜] E)
    (hA : Function.Injective A) : A.range →ₗ[𝕜] E :=
  D.comp (i.comp (LinearEquiv.ofInjective A hA).symm.toLinearMap)

/-- Claim 43319: fixed-context lifts agree exactly when their explicit global
embeddings agree; no identification of the two local source spaces is made. -/
def fixedContextOverlapAgreement : Prop :=
  ∀ (𝕜 K₁ K₂ Y₁ Y₂ V E : Type*)
    [Field 𝕜]
    [AddCommGroup K₁] [AddCommGroup K₂]
    [AddCommGroup Y₁] [AddCommGroup Y₂]
    [AddCommGroup V] [AddCommGroup E]
    [Module 𝕜 K₁] [Module 𝕜 K₂]
    [Module 𝕜 Y₁] [Module 𝕜 Y₂]
    [Module 𝕜 V] [Module 𝕜 E]
    (A₁ : K₁ →ₗ[𝕜] Y₁) (A₂ : K₂ →ₗ[𝕜] Y₂)
    (i₁ : K₁ →ₗ[𝕜] V) (i₂ : K₂ →ₗ[𝕜] V) (D : V →ₗ[𝕜] E),
    (hA₁ : Function.Injective A₁) →
    (hA₂ : Function.Injective A₂) →
    ∀ x₁ x₂, i₁ x₁ = i₂ x₂ →
      canonicalEmbeddedLift A₁ i₁ D hA₁
          ⟨A₁ x₁, ⟨x₁, rfl⟩⟩ = D (i₁ x₁) ∧
      D (i₁ x₁) = D (i₂ x₂) ∧
      D (i₂ x₂) =
        canonicalEmbeddedLift A₂ i₂ D hA₂
          ⟨A₂ x₂, ⟨x₂, rfl⟩⟩

end MathlibPlus.Open.Research.FormalizationBatch
