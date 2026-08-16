import Mathlib

namespace MathlibPlus.Open

private def addCayleyGraph {G : Type*} [AddGroup G]
    (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

private def mulCayleyGraph {G : Type*} [Group G]
    (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

def c2PowC9CIValencyFour : Prop :=
  ∀ (r : ℕ), (r = 3 ∨ r = 4 ∨ r = 5) →
    ∀ (S T : Set ((Fin r → ZMod 2) × ZMod 9)),
      0 ∉ S → (∀ x ∈ S, -x ∈ S) → S.encard = 4 →
      0 ∉ T → (∀ x ∈ T, -x ∈ T) →
      (addCayleyGraph S ≃g addCayleyGraph T) →
      ∃ α : ((Fin r → ZMod 2) × ZMod 9) ≃+ ((Fin r → ZMod 2) × ZMod 9),
        S.image α = T

private def q12A : FreeGroup (Fin 2) := FreeGroup.of 0
private def q12B : FreeGroup (Fin 2) := FreeGroup.of 1
private def q12Relators : Set (FreeGroup (Fin 2)) :=
  {q12A ^ 6, q12B ^ 2 * (q12A ^ 3)⁻¹, q12B⁻¹ * q12A * q12B * q12A}
private abbrev Q12 := FreeGroup (Fin 2) ⧸ Subgroup.normalClosure q12Relators
private abbrev C7 := Multiplicative (ZMod 7)

def q12C7CIValencies : Prop :=
  ∀ (S T : Set (C7 × Q12)),
    1 ∉ S → (∀ x ∈ S, x⁻¹ ∈ S) →
    1 ∉ T → (∀ x ∈ T, x⁻¹ ∈ T) →
    ((S.encard = 9 ∧ T.encard = 9) ∨ (S.encard = 74 ∧ T.encard = 74)) →
    (mulCayleyGraph S ≃g mulCayleyGraph T) →
    ∃ α : (C7 × Q12) ≃* (C7 × Q12), S.image α = T

end MathlibPlus.Open
