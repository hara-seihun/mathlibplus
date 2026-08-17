import MathlibPlus.Open.R1081.FactorGraphs_01a000db_a016_792b_b33f_00a9410f47c6

namespace MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim41320

open MathlibPlus.Open.R1081

abbrev F7 := Z7
abbrev Plane7 := F7 × F7

private def qShort : Set F7 := {1, -1}
private def qLong : Set F7 := {1, -1, 2, -2}
private def emptyInner : Set F7 := ∅
private def completeInner : Set F7 := {x | x ≠ 0}

/-- The four R-1148 rows, including the source graph indices. -/
def graphIndex41320 : Fin 4 → ℕ := ![49, 52, 2769, 2772]

def graphQ41320 : Fin 4 → Set F7 :=
  ![qShort, qShort, qLong, qLong]

def graphI41320 : Fin 4 → Set F7 :=
  ![emptyInner, completeInner, emptyInner, completeInner]

def graphRow41320 (i : Fin 4) : ℕ × Set F7 × Set F7 :=
  (graphIndex41320 i, graphQ41320 i, graphI41320 i)

def listedGraphRows41320 : Set (ℕ × Set F7 × Set F7) :=
  {(49, qShort, emptyInner), (52, qShort, completeInner),
    (2769, qLong, emptyInner), (2772, qLong, completeInner)}

def zeroStabilizerSet41320 (Q I : Set F7) : Set (Equiv.Perm Plane7) :=
  {σ | kernelGraphAut Q I σ ∧ σ (0, 0) = (0, 0)}

def zeroStabilizerGroup41320 (Q I : Set F7) :
    Subgroup (Equiv.Perm Plane7) :=
  Subgroup.closure (zeroStabilizerSet41320 Q I)

abbrev S6_41320 := Equiv.Perm (Fin 6)
abbrev S7_41320 := Equiv.Perm (Fin 7)
abbrev C2_41320 := Equiv.Perm (Fin 2)
abbrev ZeroStabilizerProduct41320 :=
  S6_41320 × ((Fin 6 → S7_41320) × C2_41320)

def linearPermutation41320 (σ : Equiv.Perm Plane7) : Prop :=
  ∃ L : Plane7 ≃ₗ[F7] Plane7, ∀ p : Plane7, σ p = L p

def triangularMap41320 (σ : Equiv.Perm Plane7) : Prop :=
  ∃ ε c d : F7,
    (ε = 1 ∨ ε = -1) ∧ d ≠ 0 ∧
      ∀ x y : F7, σ (x, y) = (ε * x, c * x + d * y)

/-- The zero stabilizer is the displayed direct product, has the stated
order, and its `GL(2,7)` intersection is exactly the 84 triangular maps. -/
def claim41320 : Prop :=
  Set.range graphRow41320 = listedGraphRows41320 ∧
    ∀ i : Fin 4,
      let Q := graphQ41320 i
      let I := graphI41320 i
      ((↑(zeroStabilizerGroup41320 Q I) : Set (Equiv.Perm Plane7)) =
        zeroStabilizerSet41320 Q I) ∧
      Nonempty
        (zeroStabilizerGroup41320 Q I ≃* ZeroStabilizerProduct41320) ∧
      Nat.card (zeroStabilizerGroup41320 Q I) =
        23601831786829578240000000 ∧
      (∀ σ : Equiv.Perm Plane7,
        σ ∈ zeroStabilizerSet41320 Q I ∧ linearPermutation41320 σ ↔
          triangularMap41320 σ) ∧
      Nat.card {σ : Equiv.Perm Plane7 // triangularMap41320 σ} = 84

end MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim41320
