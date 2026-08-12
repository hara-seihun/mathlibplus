import MathlibPlus.Combinatorics.Claim29410Definitions
import Mathlib.Algebra.MvPolynomial.Coeff

namespace MathlibPlus.Combinatorics.Claim29410

open scoped BigOperators

private lemma coeff_legMessage_zero (a b : ℕ) :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) a) (legMessage b) =
      if a = b then 1 else 0 := by
  classical
  simp [legMessage, MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_pow]
  by_cases hab : a = b
  · simp [hab]
  · have hba : b ≠ a := Ne.symm hab
    have hsingle :
        Finsupp.single (0 : Fin 2) b ≠ Finsupp.single (0 : Fin 2) a := by
      intro h
      rw [Finsupp.single_eq_single_iff] at h
      rcases h with ⟨_, hba'⟩ | ⟨hb, ha⟩
      · exact hba hba'
      · exact hab (hb ▸ ha ▸ rfl)
    simp [hsingle, hab]

/-- The coefficient of `u^a z^0` is the multiplicity of the length `a`.
The variable convention is `u = X 0`, `z = X 1`. -/
theorem rootedSideMessage_coeff
    (C : Multiset ℕ) (a : ℕ) :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) a) (rootedSideMessage C) =
      C.count a := by
  classical
  induction C using Multiset.induction_on with
  | empty => simp [rootedSideMessage]
  | @cons b C ih =>
      rw [show rootedSideMessage (b ::ₘ C) =
          legMessage b + rootedSideMessage C by simp [rootedSideMessage]]
      rw [MvPolynomial.coeff_add, coeff_legMessage_zero, ih,
        Multiset.count_cons]
      by_cases hab : a = b <;> simp [hab, Nat.add_comm]

/-- Among multisets of positive leg lengths, the rooted side message determines
its multiset exactly. -/
theorem rootedSideMessage_injective_on_positive :
    ∀ C D : Multiset ℕ,
      (∀ a, a ∈ C → 0 < a) →
      (∀ a, a ∈ D → 0 < a) →
      rootedSideMessage C = rootedSideMessage D → C = D := by
  intro C D hC hD hmsg
  apply Multiset.ext.mpr
  intro a
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) a)) hmsg
  rw [rootedSideMessage_coeff, rootedSideMessage_coeff] at hcoeff
  exact hcoeff

end MathlibPlus.Combinatorics.Claim29410
