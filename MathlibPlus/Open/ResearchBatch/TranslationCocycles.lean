import Mathlib

namespace MathlibPlus.Open.ResearchBatch.TranslationCocycles

abbrev H := ZMod 3 × ZMod 3
abbrev D := ZMod 3 × ZMod 3
abbrev Profile := H → D

/-- The regular translation action on profiles over `𝔽₃²`. -/
def translation (u : H) (f : Profile) : Profile :=
  fun x => f (x + u)

/-- The corresponding finite difference. -/
def difference (u : H) (f : Profile) : Profile :=
  translation u f - f

/-- An additive code is translation-invariant when it is closed under every translation. -/
def TranslationInvariant (K : AddSubgroup Profile) : Prop :=
  ∀ u : H, ∀ f : Profile, f ∈ K → translation u f ∈ K

/-- Pairwise closure, with the two evaluations required in the source statement. -/
def pairwiseClosure (K : AddSubgroup Profile) : Set Profile :=
  {q | ∀ x y : H, ∃ k : Profile, k ∈ K ∧ k x = q x ∧ k y = q y}

/-- The translation, difference, and pairwise-closure specification. -/
def claim38964 : Prop :=
  (∀ (u : H) (f : Profile) (x : H),
    translation u f x = f (x + u)) ∧
  (∀ (u : H) (f : Profile),
    difference u f = translation u f - f) ∧
  (∀ (K : AddSubgroup Profile), TranslationInvariant K →
    ∀ q : Profile,
      q ∈ pairwiseClosure K ↔
        ∀ x y : H, ∃ k : Profile, k ∈ K ∧ k x = q x ∧ k y = q y)

/-- A one-cocycle for the regular translation action. -/
def OneCocycle (z : H → Profile) : Prop :=
  ∀ u v : H, z (u + v) = z u + translation u (z v)

/-- A profile which is constant on `H`. -/
def constantProfile (d : D) : Profile :=
  fun _ => d

/-- Two profiles differ by a constant profile. -/
def EqualModuloConstants (s t : Profile) : Prop :=
  ∃ d : D, t = s + constantProfile d

/-- Every cocycle is a difference of a potential, uniquely modulo constants. -/
def claim38966 : Prop :=
  ∀ z : H → Profile, OneCocycle z →
    ∃ s : Profile,
      (∀ u : H, z u = difference u s) ∧
      (∀ t : Profile, (∀ u : H, z u = difference u t) →
        EqualModuloConstants s t)

/-- The constant `D`-plane in the profile module. -/
def constantPlane : AddSubgroup Profile where
  carrier := {f | ∃ d : D, ∀ x : H, f x = d}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro x
    rfl
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    intro x
    simp [ha x, hb x]
  neg_mem' := by
    intro f hf
    rcases hf with ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    intro x
    simp [ha x]

/-- The two basis vectors of `𝔽₃²`. -/
def e₁ : H := (1, 0)
def e₂ : H := (0, 1)

/-- The generators and all their translates used to form `K_s`. -/
def generatedGenerators (s : Profile) : Set Profile :=
  (constantPlane : Set Profile) ∪
    {q | ∃ h : H,
      q = translation h (difference e₁ s) ∨
      q = translation h (difference e₂ s)}

/-- The least-code candidate from a normalized potential. -/
def generatedTranslationCode (s : Profile) : AddSubgroup Profile :=
  AddSubgroup.closure (generatedGenerators s)

/-- The generated translation code is the least translation-invariant code containing
    the constants and both cocycle generators. -/
def claim38968 : Prop :=
  ∀ s : Profile, s 0 = 0 →
    TranslationInvariant (generatedTranslationCode s) ∧
    constantPlane ≤ generatedTranslationCode s ∧
    difference e₁ s ∈ generatedTranslationCode s ∧
    difference e₂ s ∈ generatedTranslationCode s ∧
    (∀ K : AddSubgroup Profile,
      TranslationInvariant K →
      constantPlane ≤ K →
      difference e₁ s ∈ K →
      difference e₂ s ∈ K →
      generatedTranslationCode s ≤ K)

/-- A profile lies in the finite-difference image of a pairwise closure. -/
def InDifferenceImage (K : AddSubgroup Profile) (u : H) (v : Profile) : Prop :=
  ∃ q : Profile, q ∈ pairwiseClosure K ∧ difference u q = v

/-- Normalized ternary-plane cocycles integrate in pairwise closure. -/
def claim38969 : Prop :=
  ∀ z : H → Profile,
    OneCocycle z →
    z e₁ 0 = 0 →
    z e₂ 0 = 0 →
    ∀ K : AddSubgroup Profile,
      TranslationInvariant K →
      constantPlane ≤ K →
      z e₁ ∈ K →
      z e₂ ∈ K →
      InDifferenceImage K e₁ (z e₁) ∧
      InDifferenceImage K e₂ (z e₂)

end MathlibPlus.Open.ResearchBatch.TranslationCocycles
