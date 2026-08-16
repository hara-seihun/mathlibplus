import Mathlib

namespace MathlibPlus.Open.CoprimeShellCayley

/-- The three relators in the displayed presentation of Q₁₂. -/
def q12AWord : FreeGroup (Fin 2) := FreeGroup.of 0

def q12BWord : FreeGroup (Fin 2) := FreeGroup.of 1

def q12Relators : Set (FreeGroup (Fin 2)) :=
  {q12AWord ^ 6, q12BWord ^ 2 * (q12AWord ^ 3)⁻¹,
    q12BWord⁻¹ * q12AWord * q12BWord * q12AWord}

/-- Q₁₂ = ⟨a,b | a⁶=1, b²=a³, b⁻¹ab=a⁻¹⟩, as the presented quotient. -/
abbrev Q12 : Type :=
  FreeGroup (Fin 2) ⧸ Subgroup.normalClosure q12Relators

/-- C₇ × Q₁₂, with C₇ represented by the multiplicative wrapper around
additive ZMod 7. -/
abbrev C7TimesQ12 : Type := Multiplicative (ZMod 7) × Q12

/-- Adjacency of the ordinary undirected right-Cayley graph. -/
def rightCayleyAdj (S : Set C7TimesQ12)
    (x y : C7TimesQ12) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

/-- Isomorphism of the simple graphs determined by the displayed adjacency
relation. -/
def rightCayleyGraphIso (S T : Set C7TimesQ12) : Prop :=
  ∃ e : C7TimesQ12 ≃ C7TimesQ12,
    ∀ x y, rightCayleyAdj S x y ↔ rightCayleyAdj T (e x) (e y)

/-- The exact CI assertion for the two admitted valencies. -/
def q12_coprime_shell_ci : Prop :=
  Finite C7TimesQ12 ∧
    ∀ S T : Set C7TimesQ12,
      S ⊆ ({1} : Set C7TimesQ12)ᶜ →
        T ⊆ ({1} : Set C7TimesQ12)ᶜ →
          (∀ x, x ∈ S → x⁻¹ ∈ S) →
            (∀ x, x ∈ T → x⁻¹ ∈ T) →
              Set.ncard S = Set.ncard T ∧
                (Set.ncard S = 13 ∨ Set.ncard S = 70) →
                  rightCayleyGraphIso S T →
                    ∃ α : C7TimesQ12 ≃* C7TimesQ12, α '' S = T

end MathlibPlus.Open.CoprimeShellCayley
