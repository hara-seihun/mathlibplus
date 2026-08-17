import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1108

abbrev F3 := ZMod 3
abbrev Plane := Fin 2 → F3
abbrev Codomain := Fin 3 → F3

private def basis0 : Plane := fun i => if i = 0 then 1 else 0
private def basis1 : Plane := fun i => if i = 1 then 1 else 0

private def lineRepresentative : Fin 4 → Plane
  | 0 => basis0
  | 1 => basis1
  | 2 => basis0 + basis1
  | 3 => basis0 - basis1

private def lineSubmodule (v : Plane) : Submodule F3 Plane :=
  Submodule.span F3 ({v} : Set Plane)

private def factorsThroughLine (D : Plane → Codomain) (v : Plane) : Prop :=
  ∃ φ : (Plane ⧸ lineSubmodule v) → Codomain,
    ∀ x, D x = φ (Submodule.Quotient.mk x)

private def translationPeriod (D : Plane → Codomain) (t : Plane) : Prop :=
  ∀ x, D (x + t) = D x

private def imageSpan (D : Plane → Codomain) : Submodule F3 Codomain :=
  Submodule.span F3 (Set.range D)

private def twoNonzeroQuotientValuesIndependent
    (v : Plane) (φ : (Plane ⧸ lineSubmodule v) → Codomain) : Prop :=
  ∃ u w : Plane ⧸ lineSubmodule v,
    u ≠ 0 ∧ w ≠ 0 ∧ u ≠ w ∧
      LinearIndependent F3 ![φ u, φ w]

/-- Claim 30020: after the exact D=F-F(0) normalization, a nonzero period
forces one of the four line quotients; rank at least two forces the two
nonzero quotient values to be independent and the image rank to be exactly two. -/
def nonzeroPeriodForcesLineQuotient_claim30020 : Prop :=
  ∀ F : Plane → Codomain,
    let D : Plane → Codomain := fun x => F x - F 0
    (∃ t, t ≠ 0 ∧ translationPeriod D t) →
      (∃ j : Fin 4, factorsThroughLine D (lineRepresentative j)) ∧
        (2 ≤ Module.finrank F3 (imageSpan D) →
          ∃ (j : Fin 4) (φ : (Plane ⧸ lineSubmodule (lineRepresentative j)) → Codomain),
            (∀ x, D x = φ (Submodule.Quotient.mk x)) ∧
              twoNonzeroQuotientValuesIndependent (lineRepresentative j) φ ∧
              Module.finrank F3 (imageSpan D) = 2)

end MathlibPlus.Open.ResearchFormalization.R1108
