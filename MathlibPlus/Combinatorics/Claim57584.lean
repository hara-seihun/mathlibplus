import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim57584

/-!
Claim 57584.  Roots and blocks are represented by finite types, and `B b` is
the finite set of roots in block `b`.  The two uniform-incidence hypotheses
are kept explicit, so the conclusion is exactly the double count `nr = mv`.
-/

/-- Double-counting root--block incidences gives `n * r = m * v`. -/
theorem incidence_card_identity_claim57584
    {Root Block : Type*} [Fintype Root] [Fintype Block] [DecidableEq Root]
    (B : Block → Finset Root) {r v : ℕ}
    (hr : ∀ x : Root,
      (Finset.univ.filter (fun b : Block => x ∈ B b)).card = r)
    (hv : ∀ b : Block, (B b).card = v) :
    Fintype.card Root * r = Fintype.card Block * v := by
  classical
  calc
    Fintype.card Root * r = ∑ x : Root, r := by simp
    _ = ∑ x : Root,
        (Finset.univ.filter (fun b : Block => x ∈ B b)).card := by
      simp [hr]
    _ = ∑ x : Root, ∑ b : Block, if x ∈ B b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      symm
      simpa using
        (Finset.sum_boole (fun b : Block => x ∈ B b)
          (Finset.univ : Finset Block))
    _ = ∑ b : Block, ∑ x : Root, if x ∈ B b then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b : Block, (B b).card := by
      apply Finset.sum_congr rfl
      intro b _
      symm
      simpa using
        (Finset.sum_boole (fun x : Root => x ∈ B b)
          (Finset.univ : Finset Root))
    _ = Fintype.card Block * v := by simp [hv]

end MathlibPlus.Combinatorics.Claim57584
