import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Group

/-- Relative-displacement permutations and the generated permutation group. -/
def claim53916 : Prop :=
  ∀ (G : Type*) [Finite G] [Group G] (f : G ≃ G),
    f 1 = 1 →
    let p : G → G → G := fun x s =>
      f.symm ((f x)⁻¹ * f (x * s))
    (∀ x : G, Function.Bijective (p x)) ∧
    Function.Bijective (fun s : G => s⁻¹) ∧
    ∃ pEquiv : G → Equiv.Perm G, ∃ ι : Equiv.Perm G,
      (∀ x s, pEquiv x s = p x s) ∧
      (∀ s, ι s = s⁻¹) ∧
      ∃ P_f : Subgroup (Equiv.Perm G),
        P_f = Subgroup.closure (Set.range pEquiv ∪ {ι})

/-- Directed supply, forward-closed vertex sets, and the maximum deficiency. -/
def claim53928 : Prop :=
  ∀ (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E]
    (source target : E → V) (b : V → ℤ),
    (∑ v, b v = 0) →
    let _incidence : E → V → ℤ := fun e v =>
      (if v = source e then 1 else 0) - (if v = target e then 1 else 0)
    let forwardClosed : Finset V → Prop := fun S =>
      ∀ e, source e ∈ S → target e ∈ S
    let bsum : Finset V → ℤ := fun S => ∑ v ∈ S, b v
    let M : ℤ := ∑ v, max (b v) 0
    (M = ∑ v, max (-b v) 0) ∧
    ∃ Δ : ℤ,
      (∀ S : Finset V, forwardClosed S → bsum S ≤ Δ) ∧
      (∃ S : Finset V, forwardClosed S ∧ bsum S = Δ)

end MathlibPlus.Open.ResearchFormalization.Group
