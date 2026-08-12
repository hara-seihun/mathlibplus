import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.Claim21810

open Equiv

/-- Every nontrivial cycle of a prime-order permutation has the prime length. -/
theorem cycleType_eq_prime_of_prime_order
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) {p : ℕ} (hp : Nat.Prime p)
    (horder : orderOf σ = p) :
    ∀ c ∈ σ.cycleType, c = p := by
  intro c hc
  have hdiv : c ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hc
  rw [horder] at hdiv
  exact (hp.eq_one_or_self_of_dvd c hdiv).resolve_left
    (Nat.ne_of_gt (Equiv.Perm.one_lt_of_mem_cycleType hc))

/-- A fixed-point-free prime-order permutation on 43 points is one 43-cycle. -/
theorem fixedPointFree_primeOrder_perm_43
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 43)
    (σ : Equiv.Perm α) {p : ℕ} (hp : Nat.Prime p)
    (horder : orderOf σ = p)
    (hfixed : ∀ x, σ x ≠ x) :
    p = 43 ∧ σ.IsCycle ∧ σ.support = Finset.univ := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpow : σ ^ p = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one σ
  have hpow' : σ ^ p ^ 1 = 1 := by
    simpa using hpow
  have hpdiv : p ∣ Fintype.card α := by
    by_contra hnot
    obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime
      (α := α) (p := p) (n := 1) hnot hpow'
    exact hfixed x hx
  have hpdiv43 : p ∣ 43 := by simpa [hcard] using hpdiv
  have hp43 : Nat.Prime 43 := by decide
  have hpeq : p = 43 :=
    (hp43.eq_one_or_self_of_dvd p hpdiv43).resolve_left hp.ne_one
  have hαprime : Nat.Prime (Fintype.card α) := by
    simpa [hcard] using hp43
  have horderα : orderOf σ = Fintype.card α := by
    calc
      orderOf σ = p := horder
      _ = 43 := hpeq
      _ = Fintype.card α := hcard.symm
  have hcycle : σ.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'' hαprime horderα
  have hsupport : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    exact Equiv.Perm.mem_support.mpr (hfixed x)
  exact ⟨hpeq, hcycle, hsupport⟩

/-- The contrapositive: a prime-order permutation on 43 points that is not one
43-cycle has a fixed point. -/
theorem primeOrder_perm_43_fixed_point_of_not_full_cycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 43)
    (σ : Equiv.Perm α) {p : ℕ} (hp : Nat.Prime p)
    (horder : orderOf σ = p)
    (hnot : ¬ (p = 43 ∧ σ.IsCycle ∧ σ.support = Finset.univ)) :
    ∃ x, σ x = x := by
  by_contra h
  have hfixed : ∀ x, σ x ≠ x := by
    intro x hx
    exact h ⟨x, hx⟩
  exact hnot (fixedPointFree_primeOrder_perm_43 hcard σ hp horder hfixed)

end MathlibPlus.GroupTheory.Claim21810
