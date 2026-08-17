import MathlibPlus.Open.GraphTheory.AdmittedCayleyCI
import MathlibPlus.Open.GroupTheory.Order108

namespace MathlibPlus.Open.ResearchFormalization.R1644

open MathlibPlus.Open
open MathlibPlus.Open.GroupTheory

noncomputable section

private abbrev G := C2SquaredTimesC3Cubed

private def graphAutomorphism (S : Set G) (p : Equiv.Perm G) : Prop :=
  ∀ x y : G,
    (ordinaryUndirectedCayleyGraph S).Adj (p x) (p y) ↔
      (ordinaryUndirectedCayleyGraph S).Adj x y

private def regularCopy (R : Subgroup (Equiv.Perm G)) : Prop :=
  Nonempty (R ≃* Multiplicative G) ∧
    ∀ x y : G, ∃! r : R, r.1 x = y

private def preservesCosets
    (R : Subgroup (Equiv.Perm G)) (D : AddSubgroup G) : Prop :=
  ∀ r : R, ∀ x y : G,
    y - x ∈ D ↔ r.1 y - r.1 x ∈ D

private def commonCosetSystem
    (R T : Subgroup (Equiv.Perm G)) (D : AddSubgroup G) : Prop :=
  1 < Nat.card D ∧
    Nat.card D < Nat.card G ∧
      preservesCosets R D ∧ preservesCosets T D

private def minimumCommonCosetSystem
    (R T : Subgroup (Equiv.Perm G)) (D : AddSubgroup G) : Prop :=
  commonCosetSystem R T D ∧
    ∀ E : AddSubgroup G,
      commonCosetSystem R T E → Nat.card D ≤ Nat.card E

private def regularPairInGraph
    (S : Set G) (R T : Subgroup (Equiv.Perm G))
    (D : AddSubgroup G) : Prop :=
  IdentityFreeInverseClosed S ∧
    regularCopy R ∧ regularCopy T ∧
      (∀ r : R, graphAutomorphism S r.1) ∧
        (∀ t : T, graphAutomorphism S t.1) ∧
          minimumCommonCosetSystem R T D

private def graphConjugacy
    (S : Set G) (R T : Subgroup (Equiv.Perm G)) : Prop :=
  ∃ a : Equiv.Perm G,
    graphAutomorphism S a ∧
      ∀ ρ : Equiv.Perm G,
        ρ ∈ T ↔ a.symm * ρ * a ∈ R

/-- Claim 39900: under the exact minimum common three-point block setup,
    the regular copies are conjugate in the full graph automorphism group;
    consequently no witness pair in this branch is a CI obstruction. -/
def claim39900 : Prop :=
  ∀ (S : Set G) (R T : Subgroup (Equiv.Perm G))
    (D : AddSubgroup G),
    Nat.card D = 3 →
      regularPairInGraph S R T D →
        graphConjugacy S R T

end

end MathlibPlus.Open.ResearchFormalization.R1644
