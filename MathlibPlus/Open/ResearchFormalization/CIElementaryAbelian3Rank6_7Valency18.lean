import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIElementaryAbelian3Rank6_7Valency18

abbrev vector (r : ℕ) := Fin r → ZMod 3

def identityFree {r : ℕ} (S : Set (vector r)) : Prop :=
  (0 : vector r) ∉ S

def inverseClosed {r : ℕ} (S : Set (vector r)) : Prop :=
  ∀ ⦃x : vector r⦄, x ∈ S → -x ∈ S

def ordinaryCayleyGraph {r : ℕ} (S : Set (vector r)) : SimpleGraph (vector r) :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def linearCayleyTransport {r : ℕ} (S T : Set (vector r)) : Prop :=
  ∃ L : vector r ≃ₗ[ZMod 3] vector r, L '' S = T

/-- The two valency-eighteen CI assertions on the exact ternary vector carriers. -/
def claim61441 : Prop :=
  (∀ S : Set (vector 6),
    identityFree S →
      inverseClosed S →
        S.ncard = 18 →
          AddSubgroup.closure S = ⊤ →
            (ordinaryCayleyGraph S).Connected ∧
              ∀ T : Set (vector 6),
                identityFree T →
                  inverseClosed T →
                    ordinaryCayleyGraph S ≃g ordinaryCayleyGraph T →
                      linearCayleyTransport S T) ∧
  (∀ r : ℕ, ∀ S : Set (vector r),
    identityFree S →
      inverseClosed S →
        min S.ncard (3 ^ r - 1 - S.ncard) ≤ 18 →
          ∀ T : Set (vector r),
            identityFree T →
              inverseClosed T →
                ordinaryCayleyGraph S ≃g ordinaryCayleyGraph T →
                  linearCayleyTransport S T)

end MathlibPlus.Open.ResearchFormalization.CIElementaryAbelian3Rank6_7Valency18
