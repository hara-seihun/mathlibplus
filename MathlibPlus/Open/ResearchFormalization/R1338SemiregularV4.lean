import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

namespace MathlibPlus.Open.ResearchFormalization.R1338SemiregularV4

noncomputable section

/-- Claim 30981: the exact natural `A₁₂` carrier has one conjugacy class of
semiregular Klein-four subgroups, each with three regular four-point orbits;
an odd element in its `S₁₂` normalizer prevents splitting of that class. -/
def semiregularV4ClassInA12_claim30981 : Prop :=
  let A12 := alternatingGroup (Fin 12)
  let orbit := fun (E : Subgroup (Equiv.Perm (Fin 12))) (x : Fin 12) =>
    {y : Fin 12 | ∃ g : E, (g : Equiv.Perm (Fin 12)) x = y}
  let admissible := fun E : Subgroup (Equiv.Perm (Fin 12)) =>
    E ≤ A12 ∧
      IsKleinFour E ∧
      (∀ g : E, g ≠ 1 → ∀ x : Fin 12,
        (g : Equiv.Perm (Fin 12)) x ≠ x)
  (∀ E : Subgroup (Equiv.Perm (Fin 12)), admissible E →
    (∃ reps : Fin 3 → Fin 12,
      (∀ i : Fin 3, Set.ncard (orbit E (reps i)) = 4) ∧
        (∀ i j : Fin 3, i ≠ j →
          Disjoint (orbit E (reps i)) (orbit E (reps j))) ∧
        (⋃ i : Fin 3, orbit E (reps i)) = Set.univ) ∧
      ∃ u : Equiv.Perm (Fin 12),
        u ∈ Subgroup.normalizer (E : Set (Equiv.Perm (Fin 12))) ∧
          Equiv.Perm.sign u ≠ 1) ∧
    (∀ E F : Subgroup (Equiv.Perm (Fin 12)),
      admissible E → admissible F →
        ∃ a : A12,
          ∀ g : Equiv.Perm (Fin 12),
            g ∈ E ↔
              (a : Equiv.Perm (Fin 12)) * g *
                  (a : Equiv.Perm (Fin 12))⁻¹ ∈ F)

end

end MathlibPlus.Open.ResearchFormalization.R1338SemiregularV4
