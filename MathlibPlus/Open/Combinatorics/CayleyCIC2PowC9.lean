import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The ordinary undirected Cayley graph of an additive group for an inverse-closed
connection set avoiding the identity. -/
def ordinaryUndirectedCayleyGraph {G : Type*} [AddGroup G] (S : Set G)
    (hS : ∀ s, s ∈ S → -s ∈ S) (hzero : (0 : G) ∉ S) : SimpleGraph G :=
  SimpleGraph.mk (fun x y => y - x ∈ S)
    (by
      apply Std.Symm.mk
      intro x y h
      simpa only [neg_sub] using hS (y - x) h)
    (by
      apply Std.Irrefl.mk
      intro x h
      exact hzero (by simpa using h))

/-- A Cayley graph for a connection set whose elements all have additive order two. -/
def orderTwoCayleyGraph {G : Type*} [AddGroup G] (S : Set G)
    (hsub : S ⊆ (Set.univ : Set G) \ {0})
    (horder : ∀ s ∈ S, addOrderOf s = 2) : SimpleGraph G :=
  ordinaryUndirectedCayleyGraph S
    (by
      intro s hs
      have hdiv : addOrderOf s ∣ 2 := by
        rw [horder s hs]
      have htwice : (2 : ℕ) • s = 0 :=
        (addOrderOf_dvd_iff_nsmul_eq_zero).mp hdiv
      have hadd : s + s = 0 := by
        simpa only [two_nsmul] using htwice
      rw [neg_eq_of_add_eq_zero_right hadd]
      exact hs)
    (by
      intro h
      exact (hsub h).2 (by simp))

/-- Claim 59930: the order-two four-generator Cayley graphs in
`C_2^r × C_9` have the CI property. -/
def cayleyGraphCI_C2Pow_C9 : Prop :=
  ∀ r : ℤ, 0 ≤ r →
    let G := (Fin r.toNat → ZMod 2) × ZMod 9
    ∀ (S : Set G)
      (hS : S.ncard = 4 ∧
        S ⊆ (Set.univ : Set G) \ {0} ∧
        (∀ s ∈ S, addOrderOf s = 2)),
      ∀ (T : Set G)
        (hTsub : T ⊆ (Set.univ : Set G) \ {0})
        (hTinv : ∀ t ∈ T, -t ∈ T),
        (orderTwoCayleyGraph S hS.2.1 hS.2.2 ≃g
          ordinaryUndirectedCayleyGraph T hTinv
            (by
              intro h
              exact (hTsub h).2 (by simp))) →
        ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.Combinatorics
