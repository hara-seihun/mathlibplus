import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveCayleyShear61253

noncomputable section

private abbrev F3 := ZMod 3

private def shearDefectSubmodule
    {B A : Type*} [AddCommGroup B] [AddCommGroup A]
    [Module F3 A]
    (F : B → A) (b : B) : Submodule F3 A :=
  Submodule.span F3
    {d : A | ∃ x : B, d = F b + F x - F (x + b)}

private def directedCayleyAdjacent
    {V : Type*} [AddGroup V] (S : Set V) (x y : V) : Prop :=
  y - x ∈ S

private def directedCayleyIsomorphism
    {V W : Type*} [AddGroup V] [AddGroup W]
    (S : Set V) (T : Set W) (f : V → W) : Prop :=
  Function.Bijective f ∧
    ∀ x y, directedCayleyAdjacent S x y ↔
      directedCayleyAdjacent T (f x) (f y)

private def verticalShear
    {B A : Type*} [Add B] [Add A]
    (F : B → A) : B × A → B × A :=
  fun p => (p.1, p.2 + F p.1)

private def linearVerticalShear
    {B A : Type*} [Add B] [Add A]
    (ell : B → A) : B × A → B × A :=
  fun p => (p.1, p.2 + ell p.1)

/-- Claim 61253: the exact finite-dimensional F₃ shear-defect alternatives
produce one linear correction, and every directed Cayley relation transported
by the nonlinear shear is transported by that linear correction as well. -/
def arbitraryTernaryFibrePlaneShear_claim61253 : Prop :=
  ∀ (B A : Type*)
    [AddCommGroup B] [AddCommGroup A]
    [Module F3 B] [Module F3 A]
    [FiniteDimensional F3 B] [FiniteDimensional F3 A]
    (F : B → A),
    F 0 = 0 →
      (Module.finrank F3 A ≤ 2 ∨
        (Module.finrank F3 B = 3 ∧ Module.finrank F3 A ≤ 4)) →
        ∃ ell : B →ₗ[F3] A,
          (∀ b : B,
            F b - ell b ∈ shearDefectSubmodule F b) ∧
          (∀ (S T : Set (B × A)),
            directedCayleyIsomorphism S T (verticalShear F) →
              linearVerticalShear ell '' S = T)

end

end MathlibPlus.Open.ResearchFormalization.AdaptiveCayleyShear61253
