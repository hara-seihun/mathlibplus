import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1227

/--
The centralizer assertion for a faithful prime-degree action, with the
identification of a simple group with its inner automorphisms made explicit.
The right-hand side is the image of the regular subgroup under that
identification, rather than an untyped equality between subgroups of
incompatible groups.
-/
def claim30333 : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (T : Subgroup (Equiv.Perm Ω)) (U : Subgroup T),
    Nat.Prime p ∧ 3 < p ∧ Fintype.card Ω = p ∧
      Nontrivial T ∧ IsSimpleGroup T ∧
        (¬ ∀ x y : T, x * y = y * x) ∧
      Function.Injective (fun t : T => (t : Equiv.Perm Ω)) ∧
      (∀ u v : Ω, ∃ t : T, (t : Equiv.Perm Ω) u = v) ∧
      Nat.card U = p ∧
      (∀ u v : Ω, ∃! h : U, ((h : T) : Equiv.Perm Ω) u = v) →
      ∀ φ : T ≃* T,
        ((∀ u : U, ∀ x : T,
            φ ((u : T) * x * (u : T)⁻¹) =
              (u : T) * φ x * (u : T)⁻¹) ↔
          ∃ u : U, ∀ x : T,
            φ x = (u : T) * x * (u : T)⁻¹)

end MathlibPlus.Open.ResearchFormalization.R1227
