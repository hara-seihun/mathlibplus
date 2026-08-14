import Mathlib

namespace MathlibPlus.Open.Frontier

abbrev F3Vector (r : ℕ) := Fin r → ZMod 3

def identityFree {r : ℕ} (S : Set (F3Vector r)) : Prop :=
  (0 : F3Vector r) ∉ S

def inverseClosed {r : ℕ} (S : Set (F3Vector r)) : Prop :=
  ∀ ⦃x : F3Vector r⦄, x ∈ S → -x ∈ S

def cayleyGraph {r : ℕ} (S : Set (F3Vector r)) : SimpleGraph (F3Vector r) :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def ciMinimalValencyRankSixOrSeven : Prop :=
  ∀ r : ℕ, r ∈ ({6, 7} : Set ℕ) →
    ∀ S : Set (F3Vector r),
      (cayleyGraph S).Connected →
      identityFree S →
      inverseClosed S →
      S.ncard = 2 * r →
      ∀ T : Set (F3Vector r),
        identityFree T →
        inverseClosed T →
        cayleyGraph S ≃g cayleyGraph T →
        ∃ A : F3Vector r ≃ₗ[ZMod 3] F3Vector r, A '' S = T

end MathlibPlus.Open.Frontier
