import Mathlib

namespace MathlibPlus.Open.R1834

abbrev G := (Fin 2 → ZMod 2) × (Fin 3 → ZMod 3)
abbrev PermutationGroup := Subgroup (Equiv.Perm G)

private def ordinaryConnectionSet (S : Set G) : Prop :=
  (0 : G) ∉ S ∧ ∀ s : G, s ∈ S ↔ -s ∈ S

private def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

private def graphAutomorphism (S : Set G) (σ : Equiv.Perm G) : Prop :=
  ∀ x y : G,
    cayleyAdjacency S (σ x) (σ y) ↔ cayleyAdjacency S x y

private def regularCopy (R : PermutationGroup) : Prop :=
  ∀ x y : G, ∃! r : R, r.1 x = y

private def copyOfG (R : PermutationGroup) : Prop :=
  Nonempty (R ≃* Multiplicative G)

private def conjugateSubgroups
    (σ : Equiv.Perm G) (R T : PermutationGroup) : Prop :=
  ∀ ρ : Equiv.Perm G,
    ρ ∈ T ↔ σ.symm * ρ * σ ∈ R

private def fullSymmetricConjugacy (R T : PermutationGroup) : Prop :=
  regularCopy R → regularCopy T → copyOfG R → copyOfG T →
    ∃ σ : Equiv.Perm G, conjugateSubgroups σ R T

/-- Claim 32747: the fixed group `C₂² × C₃³` is an ordinary undirected
CI-group, expressed over every actual loopless inverse-closed Cayley carrier
and every pair of regular copies inside that graph's automorphism group. -/
def claim32747 : Prop :=
  Nat.card G = 108 ∧
    ∀ S : Set G, ordinaryConnectionSet S →
      ∀ R T : PermutationGroup,
        regularCopy R → regularCopy T →
        copyOfG R → copyOfG T →
        (∀ r : R, graphAutomorphism S r.1) →
        (∀ t : T, graphAutomorphism S t.1) →
        (∃ σ : Equiv.Perm G,
          graphAutomorphism S σ ∧ conjugateSubgroups σ R T) ∧
        ((S = (∅ : Set G) ∨ S = {x : G | x ≠ 0}) →
          fullSymmetricConjugacy R T)

end MathlibPlus.Open.R1834
