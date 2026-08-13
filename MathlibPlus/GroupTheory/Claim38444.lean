import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim38444

/-- A finite-group support cannot meet a left stabilizer when the support omits
identity: invariance under left multiplication by a support element forces all
positive powers of that element into the support. -/
theorem nonlinearSupport_disjoint_leftStabilizer_claim38444
    {G : Type*} [Finite G] [Group G]
    (N L : Set G) (hone : (1 : G) ∉ N)
    (hstab : ∀ a ∈ L, (fun x : G => a * x) '' N = N) :
    N ∩ L = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro a ha
  have haN : a ∈ N := ha.1
  have haL : a ∈ L := ha.2
  have hpow : ∀ k : ℕ, 1 ≤ k → a ^ k ∈ N := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using haN
    | succ k hk ih =>
        rw [pow_succ']
        have : a * a ^ k ∈ (fun x : G => a * x) '' N := ⟨a ^ k, ih, rfl⟩
        simpa [hstab a haL] using this
  have horder : 0 < orderOf a := orderOf_pos a
  have honeN : (1 : G) ∈ N := by
    rw [← pow_orderOf_eq_one a]
    exact hpow (orderOf a) horder
  exact hone honeN

end MathlibPlus.GroupTheory.Claim38444
