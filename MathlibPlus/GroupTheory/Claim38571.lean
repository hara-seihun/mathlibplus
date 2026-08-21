-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

open scoped BigOperators

namespace MathlibPlus.GroupTheory

/-- Claim 38571: the two concrete Sylow-5 cardinalities and the centralizer
of a five-cycle in `S₅`. -/
theorem smallSymmetricGroupFiveLocalFacts_claim38571 :
    (∀ P : Sylow 5 (Equiv.Perm (Fin 5)), Nat.card P = 5) ∧
      (∀ P : Sylow 5 (Equiv.Perm (Fin 6)), Nat.card P = 5) ∧
      (∀ g : Equiv.Perm (Fin 5), g.cycleType = {5} →
        Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 5)))) = 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have hcard6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have h5 : Nat.factorization 120 5 = 1 := by native_decide
  have h6 : Nat.factorization 720 5 = 1 := by native_decide
  have hP5 (P : Sylow 5 (Equiv.Perm (Fin 5))) : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity P, hcard5, h5]
    norm_num
  have hP6 (P : Sylow 5 (Equiv.Perm (Fin 6))) : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity P, hcard6, h6]
    norm_num
  refine ⟨hP5, hP6, ?_⟩
  intro g hg
  rw [Equiv.Perm.nat_card_centralizer g, hg]
  norm_num

end MathlibPlus.GroupTheory
