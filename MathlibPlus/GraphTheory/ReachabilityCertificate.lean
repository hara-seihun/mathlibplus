import Mathlib

namespace MathlibPlus.GraphTheory.Reachability

/-!
Formalization of admitted claim 52631.  A path is represented by a finite
`Fin (n + 1)`-indexed sequence; its first vertex is the entry state, its last
vertex is the rank-one exit, and `activeSucc` records each consecutive edge.
-/

/-- A finite path from an entry state to a rank-one exit has a prefix ending at
its first rank-one state.  That prefix contains an entry state, and every
non-exit vertex has the next path vertex as an active successor. -/
theorem firstRankOnePathCertificate
    {α : Type*} (entry rankOne : α → Prop)
    (activeSucc : α → α → Prop) (n : ℕ)
    (path : Fin (n + 1) → α)
    (hentry : entry (path 0))
    (hexit : rankOne (path (Fin.last n)))
    (hstep : ∀ i : Fin n,
      activeSucc
        (path ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (path ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) :
    ∃ k : Fin (n + 1),
      rankOne (path k) ∧
      (∀ j : Fin (n + 1), j.val < k.val → ¬rankOne (path j)) ∧
      (∃ j : Fin (n + 1), j.val ≤ k.val ∧ entry (path j)) ∧
      (∀ i : Fin n, i.val < k.val →
        activeSucc
          (path ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (path ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ hk : k < n + 1, rankOne (path ⟨k, hk⟩)
  have hP : ∃ k, P k := by
    refine ⟨n, ?_⟩
    refine ⟨Nat.lt_succ_self n, ?_⟩
    have hlast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      rfl
    exact hlast ▸ hexit
  let kNat : ℕ := Nat.find hP
  have hkP : P kNat := Nat.find_spec hP
  rcases hkP with ⟨hklt, hkRank⟩
  let k : Fin (n + 1) := ⟨kNat, hklt⟩
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · simpa [k] using hkRank
  · intro j hj hbad
    have hlt : j.val < Nat.find hP := by
      change j.val < kNat
      simpa [k] using hj
    have hmin : ¬P j.val := @Nat.find_min P _ hP j.val hlt
    apply hmin
    exact ⟨j.isLt, by simpa using hbad⟩
  · refine ⟨⟨0, Nat.zero_lt_succ n⟩, Nat.zero_le _, ?_⟩
    exact hentry
  · intro i _
    exact hstep i

end MathlibPlus.GraphTheory.Reachability
