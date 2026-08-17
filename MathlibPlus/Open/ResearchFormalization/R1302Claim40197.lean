import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40197

abbrev C7 := Multiplicative (ZMod 7)
abbrev Q12 := QuaternionGroup 3
abbrev G84 := C7 × Q12

abbrev BlockPoint {Ω : Type*} (B : Finset (Set Ω)) :=
  {U : Set Ω // U ∈ B}
abbrev BlockPerm {Ω : Type*} (B : Finset (Set Ω)) :=
  Equiv.Perm (BlockPoint B)

/-- A regular permutation copy of the concrete group `C₇ × Q₁₂`. -/
def regularG84 {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y) ∧
    Nonempty (G84 ≃* R)

/-- A finite system of 21 disjoint four-point blocks covering its carrier. -/
def fourBlockSystem {Ω : Type*}
    (B : Finset (Set Ω)) : Prop :=
  B.card = 21 ∧
    (∀ U ∈ B, U.ncard = 4) ∧
      (∀ U ∈ B, ∀ V ∈ B, U ≠ V → Disjoint U V) ∧
        (∀ x : Ω, ∃ U ∈ B, x ∈ U)

/-- The generated ambient permutation group. -/
def generatedPair {Ω : Type*}
    (R T : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))

/-- The actual action on the subtype of displayed blocks. -/
def inducedBlockAction {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω))
    (B : Finset (Set Ω))
    (ρ : X →* BlockPerm B) : Prop :=
  ∀ g : X, ∀ U : BlockPoint B,
    ((ρ g) U).1 = (g : Equiv.Perm Ω) '' U.1

/-- A normal seven-subgroup of `R`. -/
def normalIn {Ω : Type*}
    (R P : Subgroup (Equiv.Perm Ω)) : Prop :=
  P ≤ R ∧
    ∀ r : R, ∀ p : P,
      (r : Equiv.Perm Ω) * (p : Equiv.Perm Ω) *
          (r : Equiv.Perm Ω)⁻¹ ∈ P

/-- The finite seven-subgroups used in the definition of `O₇`. -/
def sevenSubgroup {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ n : ℕ, Nat.card P = 7 ^ n

/-- `P` is the largest normal seven-subgroup of `R`, namely `O₇(R)`. -/
def isO7 {Ω : Type*}
    (R P : Subgroup (Equiv.Perm Ω)) : Prop :=
  P ≤ R ∧
    sevenSubgroup P ∧
      normalIn R P ∧
        ∀ N : Subgroup (Equiv.Perm Ω),
          N ≤ R → sevenSubgroup N → normalIn R N → N ≤ P

/-- The actual image of a subgroup's block action. -/
def inducedImage {Ω : Type*}
    (P X : Subgroup (Equiv.Perm Ω))
    (hPX : P ≤ X)
    (B : Finset (Set Ω))
    (ρ : X →* BlockPerm B) : Subgroup (BlockPerm B) :=
  (ρ.comp (P.inclusion hPX)).range

/-- A finite seven-subgroup used in the quotient Sylow step. -/
def sevenGroup {α : Type*}
    (H : Subgroup (Equiv.Perm α)) : Prop :=
  ∃ n : ℕ, Nat.card H = 7 ^ n

/-- The Sylow-seven condition inside a quotient permutation group. -/
def sylowSeven {α : Type*}
    (Y V : Subgroup (Equiv.Perm α)) : Prop :=
  V ≤ Y ∧
    sevenGroup V ∧
      ∀ W : Subgroup (Equiv.Perm α),
        W ≤ Y → sevenGroup W → Nat.card W ≤ Nat.card V

/-- Semiregularity of an induced quotient subgroup. -/
def semiregular {α : Type*}
    (H : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ h : H, h ≠ 1 → ∀ u : α,
    (h : Equiv.Perm α) u ≠ u

/-- The orbit of a block-point under an induced subgroup. -/
def orbitOf {Ω : Type*} {B : Finset (Set Ω)}
    (H : Subgroup (BlockPerm B)) (u : BlockPoint B) : Set (BlockPoint B) :=
  {v | ∃ h : H, (h : BlockPerm B) u = v}

/-- The partition into induced block orbits. -/
def orbitPartition {Ω : Type*} {B : Finset (Set Ω)}
    (H : Subgroup (BlockPerm B)) : Set (Set (BlockPoint B)) :=
  Set.range (orbitOf H)

/-- Conjugation by the literal quotient permutation. -/
def conjugateSubgroup {α : Type*}
    (x : Equiv.Perm α)
    (H : Subgroup (Equiv.Perm α)) : Subgroup (Equiv.Perm α) :=
  H.map (MulAut.conj x).toMonoidHom

/-- The inverse image in `Ω` of a collection of displayed blocks. -/
def pullbackBlockSet {Ω : Type*}
    (B : Finset (Set Ω))
    (S : Set (BlockPoint B)) : Set Ω :=
  {x | ∃ U : BlockPoint B, U ∈ S ∧ x ∈ U.1}

/-- Pulling an orbit partition back through `Ω → 𝔅`. -/
def pullbackOrbitPartition {Ω : Type*}
    (B : Finset (Set Ω))
    (H : Subgroup (BlockPerm B)) : Set (Set Ω) :=
  (fun S : Set (BlockPoint B) => pullbackBlockSet B S) '' orbitPartition H

/-- The concrete meaning of a three-block coarsening of the original system:
each coarse member is the union of seven original four-point blocks, the
coarse members are disjoint and cover `Ω`, and each has size 28. -/
def threeBlockCoarsening {Ω : Type*}
    (B : Finset (Set Ω))
    (C : Set (Set Ω)) : Prop :=
  C.ncard = 3 ∧
    (∀ D ∈ C, D.ncard = 7 * 4 ∧ D.ncard = 28) ∧
      (∀ D ∈ C, ∃ S : Set (BlockPoint B),
        S.ncard = 7 ∧ D = pullbackBlockSet B S) ∧
        (∀ D ∈ C, ∀ E ∈ C, D = E ∨ Disjoint D E) ∧
          (∀ x : Ω, ∃ D ∈ C, x ∈ D)

/-- Claim 40197: the first quotient conjugator lifts to `X`; the common
three-part orbit partition on the 21 blocks pulls back to three 28-point
coarse blocks, fixed setwise by `P` and by the conjugate `Qˣ`. -/
def claim40197 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω],
    Fintype.card Ω = 84 →
      ∀ (B : Finset (Set Ω))
        (R T X : Subgroup (Equiv.Perm Ω))
        (ρX : X →* BlockPerm B),
        fourBlockSystem B →
        regularG84 R →
        regularG84 T →
        X = generatedPair R T →
        (hRX : R ≤ X) →
        (hTX : T ≤ X) →
        inducedBlockAction X B ρX →
        ∀ (P Q : Subgroup (Equiv.Perm Ω)),
          (hP : isO7 R P) →
          (hQ : isO7 T Q) →
          let Pbar := inducedImage P X (hP.1.trans hRX) B ρX
          let Qbar := inducedImage Q X (hQ.1.trans hTX) B ρX
          ∀ (Vbar : Subgroup (BlockPerm B))
            (xbar : BlockPerm B),
            xbar ∈ ρX.range →
            sylowSeven ρX.range Vbar →
            Pbar ≤ Vbar →
            conjugateSubgroup xbar Qbar ≤ Vbar →
            Nat.card Pbar = 7 →
            Nat.card Qbar = 7 →
            semiregular Pbar →
            semiregular Qbar →
            orbitPartition Pbar = orbitPartition Vbar →
            orbitPartition Vbar =
              orbitPartition (conjugateSubgroup xbar Qbar) →
            (∀ u : BlockPoint B, (orbitOf Pbar u).ncard = 7) →
            (orbitPartition Pbar).ncard = 3 →
            ∃ x : X,
              ρX x = xbar ∧
                let C := pullbackOrbitPartition B Pbar
                C = pullbackOrbitPartition B Vbar ∧
                  C = pullbackOrbitPartition B
                    (conjugateSubgroup xbar Qbar) ∧
                    threeBlockCoarsening B C ∧
                      (∀ p : P, ∀ D ∈ C,
                        (p : Equiv.Perm Ω) '' D = D) ∧
                        (∀ q : conjugateSubgroup (x : Equiv.Perm Ω) Q,
                          ∀ D ∈ C,
                            (q : Equiv.Perm Ω) '' D = D)

end MathlibPlus.Open.ResearchFormalization.R1302Claim40197
