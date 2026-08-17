import Mathlib

namespace MathlibPlus.GroupTheory

universe u v

/-- The injective-to-surjective full-shift property for finite discrete alphabets. -/
def IsSurjunctive (G : Type u) [Group G] : Prop :=
  ∀ (A : Type v) [Fintype A] [TopologicalSpace A] [DiscreteTopology A],
    ∀ f : (G → A) → (G → A),
      Continuous f →
        (∀ (g : G) (x : G → A) (h : G),
          f (fun k => x (g⁻¹ * k)) h = f x (g⁻¹ * h)) →
          Function.Injective f → Function.Surjective f

/-- The reverse surjective-to-injective full-shift property. -/
def IsInjunctive (G : Type u) [Group G] : Prop :=
  ∀ (A : Type v) [Fintype A] [TopologicalSpace A] [DiscreteTopology A],
    ∀ f : (G → A) → (G → A),
      Continuous f →
        (∀ (g : G) (x : G → A) (h : G),
          f (fun k => x (g⁻¹ * k)) h = f x (g⁻¹ * h)) →
          Function.Surjective f → Function.Injective f

end MathlibPlus.GroupTheory
