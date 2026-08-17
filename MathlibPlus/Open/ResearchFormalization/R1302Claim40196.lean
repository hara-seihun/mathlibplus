import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40196

/-- The orbit of a point under a permutation subgroup. -/
def orbitOf {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (u : Ω) : Set Ω :=
  {v | ∃ h : H, (h : Equiv.Perm Ω) u = v}

/-- The orbit partition of a permutation subgroup. -/
def orbitPartition {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  Set.range (orbitOf H)

/-- No nonidentity element fixes a point. -/
def semiregular {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ h : H, h ≠ 1 → ∀ u : Ω,
    (h : Equiv.Perm Ω) u ≠ u

/-- An order-seven subgroup with exactly three seven-point orbits. -/
def orderSevenWithThreeOrbits {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nat.card H = 7 ∧
    semiregular H ∧
      (∀ u : Ω, (orbitOf H u).ncard = 7) ∧
        (orbitPartition H).ncard = 3

/-- A finite seven-group, used in the Sylow predicate. -/
def sevenGroup {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ n : ℕ, Nat.card H = 7 ^ n

/-- The Sylow-seven condition: containment, seven-power order, and maximal
seven-power order among subgroups of the acting group. -/
def sylowSeven {Ω : Type*}
    (Y V : Subgroup (Equiv.Perm Ω)) : Prop :=
  V ≤ Y ∧
    sevenGroup V ∧
      ∀ W : Subgroup (Equiv.Perm Ω),
        W ≤ Y → sevenGroup W → Nat.card W ≤ Nat.card V

/-- Conjugation of a permutation subgroup by an actual permutation. -/
def conjugateSubgroup {Ω : Type*}
    (x : Equiv.Perm Ω)
    (H : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  H.map (MulAut.conj x).toMonoidHom

/-- Every orbit of `V` contains one of the indicated `P`-orbits and has a
seven-power cardinality. -/
def containsOrbitAndHasSevenPower {Ω : Type*}
    (P V : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ u : Ω,
    (∃ v : Ω, orbitOf P v ⊆ orbitOf V u) ∧
      (∃ n : ℕ, (orbitOf V u).ncard = 7 ^ n)

/-- The orbit-size squeeze used after a Sylow conjugation. -/
def sevenOrbitSqueeze {Ω : Type*}
    (V : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ u : Ω, 7 ≤ (orbitOf V u).ncard) ∧
    (∀ u : Ω, (orbitOf V u).ncard = 7)

/-- Claim 40196: for the exact 21-point action, Sylow conjugacy supplies the
quotient conjugator and the prime-power orbit squeeze makes the three orbit
partitions coincide.  The conjugator is a conclusion, not an added premise. -/
def claim40196 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω],
    Fintype.card Ω = 21 →
      ∀ (Y P Q V : Subgroup (Equiv.Perm Ω)),
        P ≤ Y →
        Q ≤ Y →
        orderSevenWithThreeOrbits P →
        orderSevenWithThreeOrbits Q →
        sylowSeven Y V →
        P ≤ V →
        ∃ x : Y,
          let Qx := conjugateSubgroup (x : Equiv.Perm Ω) Q
          Qx ≤ V ∧
            containsOrbitAndHasSevenPower P V ∧
              sevenOrbitSqueeze V ∧
                (21 : ℕ) < 49 ∧
                  (∀ u : Ω, (orbitOf Qx u).ncard = 7) ∧
                    (∀ u : Ω,
                      (∃ v : Ω, orbitOf Qx v ⊆ orbitOf V u) ∧
                        (∃ n : ℕ, (orbitOf V u).ncard = 7 ^ n)) ∧
                      (∀ u : Ω, 7 ≤ (orbitOf V u).ncard) ∧
                        orbitPartition P = orbitPartition V ∧
                          orbitPartition V = orbitPartition Qx

end MathlibPlus.Open.ResearchFormalization.R1302Claim40196
