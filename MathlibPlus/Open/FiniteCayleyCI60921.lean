import Mathlib

namespace MathlibPlus.Open.FiniteCayleyCI60921

private def presentationRelators (m : ℕ) : Set (FreeGroup (Fin 2)) :=
  {r | r = (FreeGroup.of (0 : Fin 2)) ^ m ∨
    r = (FreeGroup.of (1 : Fin 2)) ^ 8 ∨
    r = FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
      (FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of (0 : Fin 2)}

private abbrev presentedE (m : ℕ) := PresentedGroup (presentationRelators m)

private def ordinaryCayleyGraph {G : Type} [Group G] (U : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => ∃ u ∈ U, x⁻¹ * y = u)

private def inverseClosed {G : Type} [Group G] (U : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ U → x⁻¹ ∈ U

/-- The admitted ordinary CI claim for Sylow-2-supported sets in `E(C_m,8)`. -/
def sylowTwoSupportedOrdinaryCI : Prop :=
  ∀ (m : ℕ), 1 ≤ m → Odd m →
    ∀ (S T : Set (presentedE m)),
      S ⊆ {x | x ≠ 1} → T ⊆ {x | x ≠ 1} →
      inverseClosed S → inverseClosed T →
      (∃ P : Sylow 2 (presentedE m),
        S ⊆ (P.toSubgroup : Set (presentedE m))) →
      SimpleGraph.Iso
        (ordinaryCayleyGraph S) (ordinaryCayleyGraph T) →
      ∃ α : presentedE m ≃* presentedE m, α '' S = T

end MathlibPlus.Open.FiniteCayleyCI60921
