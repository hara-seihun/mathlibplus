import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Linear

noncomputable section

/-- Invariance of a direct-sum section under the shear
    `(a,b) ↦ (a+s(b),b)`. -/
def shearInvariant
    {𝕜 A B : Type*} [Field 𝕜]
    [AddCommGroup A] [AddCommGroup B]
    [Module 𝕜 A] [Module 𝕜 B]
    (s : B →ₗ[𝕜] A) (A' : Submodule 𝕜 A) (B' : Submodule 𝕜 B) : Prop :=
  ∀ a b, a ∈ A' → b ∈ B' → a + s b ∈ A'

/-- The invariant direct-sum sections are exactly those whose fibre contains
    the potential image. -/
def invariantDirectSumSections : Prop :=
  ∀ {𝕜 A B : Type*} [Field 𝕜]
    [AddCommGroup A] [AddCommGroup B]
    [Module 𝕜 A] [Module 𝕜 B]
    (s : B →ₗ[𝕜] A) (A' : Submodule 𝕜 A) (B' : Submodule 𝕜 B),
    shearInvariant s A' B' ↔ Submodule.map s B' ≤ A'

/-- The image fibre is the smallest invariant fibre, in particular for a
    three-dimensional base subspace. -/
def smallestInvariantFibre : Prop :=
  ∀ {𝕜 A B : Type*} [Field 𝕜]
    [AddCommGroup A] [AddCommGroup B]
    [Module 𝕜 A] [Module 𝕜 B]
    (s : B →ₗ[𝕜] A) (B' : Submodule 𝕜 B),
    Module.finrank 𝕜 B' = 3 →
      shearInvariant s (Submodule.map s B') B' ∧
      ∀ A' : Submodule 𝕜 A,
        shearInvariant s A' B' → Submodule.map s B' ≤ A'

/-- Both parts of the invariant-section claim for an explicitly supplied
    coefficient field and pair of spaces. -/
def invariantDirectSumSectionsClaim
    {𝕜 A B : Type*} [Field 𝕜]
    [AddCommGroup A] [AddCommGroup B]
    [Module 𝕜 A] [Module 𝕜 B]
    (s : B →ₗ[𝕜] A) : Prop :=
  (∀ (A' : Submodule 𝕜 A) (B' : Submodule 𝕜 B),
    shearInvariant s A' B' ↔ Submodule.map s B' ≤ A') ∧
  (∀ (B' : Submodule 𝕜 B), Module.finrank 𝕜 B' = 3 →
    shearInvariant s (Submodule.map s B') B' ∧
      ∀ A' : Submodule 𝕜 A,
        shearInvariant s A' B' → Submodule.map s B' ≤ A')

end
end MathlibPlus.Open.ResearchFormalizationBatch.Linear
