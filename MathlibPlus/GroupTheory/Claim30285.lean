import Mathlib

namespace MathlibPlus.GroupTheory.Claim30285

/-!
Formalization of admitted claim 30285.  The source's `L_N` is written
explicitly as the set of group elements whose left multiplication preserves
`N`; the phrase "by definition of N" is represented by `1 ∉ N`.
-/

/-- A finite-group subset excluding the identity is disjoint from its left
stabilizer. -/
theorem leftStabilizer_disjoint_claim30285
    {G : Type*} [Group G] [Finite G]
    (N : Set G) (hOne : (1 : G) ∉ N) :
    N ∩ {a : G | ∀ x, x ∈ N → a * x ∈ N} = ∅ := by
  ext a
  constructor
  · rintro ⟨haN, haL⟩
    change ∀ x, x ∈ N → a * x ∈ N at haL
    have hP : ∀ n : ℕ, 0 < n → a ^ n ∈ N := by
      intro n
      induction n with
      | zero =>
          intro hn
          omega
      | succ n ih =>
          intro hn
          cases n with
          | zero =>
              simpa using haN
          | succ n =>
              have hprev : a ^ (Nat.succ n) ∈ N := ih (by omega)
              have hnext := haL (a ^ (Nat.succ n)) hprev
              simpa [pow_succ'] using hnext
    have horder : a ^ orderOf a ∈ N := hP (orderOf a) (orderOf_pos a)
    have hOneN : (1 : G) ∈ N := by
      simpa only [pow_orderOf_eq_one] using horder
    exact (hOne hOneN).elim
  · intro ha
    simp at ha

end MathlibPlus.GroupTheory.Claim30285
