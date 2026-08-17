import MathlibPlus.Open.ResearchFormalization.R1416BlockClaims

namespace MathlibPlus.Open.ResearchFormalization.R1416

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

/-- Conjugation of a subgroup inside the concrete order-21 Frobenius group. -/
def conjugateSubgroup36966 {G : Type*} [Group G]
    (g : G) (H : Subgroup G) : Subgroup G :=
  H.map ((MulAut.conj g : G ≃* G).toMonoidHom)

/-- Claim 36966: the complete subgroup lattice of the concrete
order-21 model of C₇:C₃, including the complement orbit and core data. -/
def claim36966 : Prop :=
  letI : Fintype Frobenius21 := Fintype.ofFinite Frobenius21
  letI : Fintype (Subgroup Frobenius21) :=
    Fintype.ofFinite (Subgroup Frobenius21)
  ∃ (N U₀ : Subgroup Frobenius21),
    Nat.card N = 7 ∧
    N.Normal ∧
    Nat.card U₀ = 3 ∧
    (∀ K : Subgroup Frobenius21,
      Nat.card K = 3 →
        K ⊓ N = (⊥ : Subgroup Frobenius21) ∧
        K ⊔ N = (⊤ : Subgroup Frobenius21) ∧
        coreOf K = (⊥ : Subgroup Frobenius21)) ∧
    Nat.card {K : Subgroup Frobenius21 // Nat.card K = 3} = 7 ∧
    (∀ K : Subgroup Frobenius21,
      K = (⊥ : Subgroup Frobenius21) ∨
        K = N ∨
        K = (⊤ : Subgroup Frobenius21) ∨
        (∃ g : Frobenius21,
          K = conjugateSubgroup36966 g U₀)) ∧
    (∀ K : Subgroup Frobenius21,
      Nat.card K = 3 →
        ∃ g : Frobenius21, K = conjugateSubgroup36966 g U₀) ∧
    (∀ N' : Subgroup Frobenius21,
      Nat.card N' = 7 → N'.Normal → N' = N) ∧
    (⊥ : Subgroup Frobenius21).Normal ∧
    coreOf (⊥ : Subgroup Frobenius21) = (⊥ : Subgroup Frobenius21) ∧
    coreOf N = N ∧
    (⊤ : Subgroup Frobenius21).Normal ∧
    coreOf (⊤ : Subgroup Frobenius21) = (⊤ : Subgroup Frobenius21)

/-- Claim 36967: every subgroup of a coprime finite abelian product with the
concrete order-21 Frobenius group splits as a product subgroup. -/
def claim36967 : Prop :=
  ∀ (A : Type*) [Fintype A] [CommGroup A],
    Nat.gcd (Nat.card A) 21 = 1 →
      ∀ H : Subgroup (A × Frobenius21),
        ∃ C : Subgroup A, ∃ U : Subgroup Frobenius21,
          H = C.prod U

end

end MathlibPlus.Open.ResearchFormalization.R1416
