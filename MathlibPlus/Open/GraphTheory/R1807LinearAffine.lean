import Mathlib

namespace MathlibPlus.Open.GraphTheory.R1807

abbrev W := Fin 2 → ZMod 7
abbrev GL2 := W ≃ₗ[ZMod 7] W

/-- A subspace is invariant under a multiplier subgroup. -/
def invariant (K : Subgroup GL2) (V : Submodule (ZMod 7) W) : Prop :=
  ∀ A : K, ∀ x : W, x ∈ V → A.1 x ∈ V

/-- Irreducibility is stated as the absence of proper nonzero invariant subspaces. -/
def irreducible (K : Subgroup GL2) : Prop :=
  ∀ V : Submodule (ZMod 7) W, invariant K V → V = ⊥ ∨ V = ⊤

/-- Claim 32463: an irreducible multiplier group leaves only zero or all of the
translation plane as an invariant stabilizer subspace. -/
def claim32463_irreducibleStabilizerDichotomy : Prop :=
  ∀ K : Subgroup GL2, ∀ T : Submodule (ZMod 7) W,
    irreducible K → invariant K T → T = ⊥ ∨ T = ⊤

/-- The exact notion of a conjugacy class of subgroups used by the census. -/
def conjugateSubgroups (K L : Subgroup GL2) : Prop :=
  ∃ g : GL2, ∀ x : GL2, x ∈ K ↔ g * x * g⁻¹ ∈ L

/-- Genuine seven-torsion means an element of order exactly seven. -/
def hasGenuineSevenTorsion (K : Subgroup GL2) : Prop :=
  ∃ x : K, orderOf x = 7

/-- Claim 32468: the subgroup census and the four irreducible seven-torsion
classes are retained as an explicit finite representative statement. -/
def claim32468_irreducibleSevenTorsionCensus : Prop :=
  Nat.card GL2 = 2016 ∧
  (∃ representatives : Fin 84 → Subgroup GL2,
    (∀ i j, conjugateSubgroups (representatives i) (representatives j) → i = j) ∧
    (∀ K : Subgroup GL2, ∃ i, conjugateSubgroups K (representatives i))) ∧
  (∃ K336 K672 K1008 K2016 : Subgroup GL2,
    Nat.card K336 = 336 ∧ Nat.card K672 = 672 ∧
    Nat.card K1008 = 1008 ∧ Nat.card K2016 = 2016 ∧
    irreducible K336 ∧ irreducible K672 ∧
    irreducible K1008 ∧ irreducible K2016 ∧
    hasGenuineSevenTorsion K336 ∧ hasGenuineSevenTorsion K672 ∧
    hasGenuineSevenTorsion K1008 ∧ hasGenuineSevenTorsion K2016 ∧
    (¬ conjugateSubgroups K336 K672) ∧
    (¬ conjugateSubgroups K336 K1008) ∧
    (¬ conjugateSubgroups K336 K2016) ∧
    (¬ conjugateSubgroups K672 K1008) ∧
    (¬ conjugateSubgroups K672 K2016) ∧
    (¬ conjugateSubgroups K1008 K2016) ∧
    (∀ K : Subgroup GL2,
      irreducible K → hasGenuineSevenTorsion K →
        conjugateSubgroups K K336 ∨ conjugateSubgroups K K672 ∨
        conjugateSubgroups K K1008 ∨ conjugateSubgroups K K2016))

/-- Claim 32469: an irreducible translation stabilizer has cardinality one or
49, so no intermediate invariant line occurs. -/
def claim32469_noIntermediateInvariantTranslationLine : Prop :=
  ∀ K : Subgroup GL2, ∀ T : Submodule (ZMod 7) W,
    irreducible K → invariant K T →
      Nat.card T = 1 ∨ Nat.card T = 49

end MathlibPlus.Open.GraphTheory.R1807
