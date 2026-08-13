import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

private theorem potential_sum_telescope_aux_claim54879
    {α β : Type*} [AddCommGroup β] (f : α → β) :
    ∀ (n : ℕ) (p : Fin (n + 1) → α),
      (∑ k : Fin n, (f (p k.castSucc) - f (p k.succ))) =
        f (p 0) - f (p (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro p
      simp
  | succ n ih =>
      intro p
      rw [Fin.sum_univ_succ]
      have htail := ih (fun k : Fin (n + 1) => p k.succ)
      have hindex : ∀ i : Fin n, i.succ.castSucc = i.castSucc.succ := by
        intro i
        apply Fin.ext
        rfl
      have htail' :
          (∑ i : Fin n, (f (p i.succ.castSucc) - f (p i.succ.succ))) =
            f (p 1) - f (p (Fin.last (n + 1))) := by
        calc
          (∑ i : Fin n, (f (p i.succ.castSucc) - f (p i.succ.succ))) =
              ∑ i : Fin n, (f (p i.castSucc.succ) - f (p i.succ.succ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hindex i]
          _ = f (p 1) - f (p (Fin.last n).succ) := htail
          _ = f (p 1) - f (p (Fin.last (n + 1))) := by
            rw [show (Fin.last n).succ = Fin.last (n + 1) by
              apply Fin.ext
              rfl]
      rw [htail']
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      abel

/-- The potential differences on a finite walk telescope to its endpoint
values.  This is the kernel-checked scalar part of claim 54879. -/
theorem potential_sum_telescope_claim54879
    {α β : Type*} [AddCommGroup β] (f : α → β) (n : ℕ)
    (p : Fin (n + 1) → α) :
    (∑ k : Fin n, (f (p k.castSucc) - f (p k.succ))) =
      f (p 0) - f (p (Fin.last n)) :=
  potential_sum_telescope_aux_claim54879 f n p

/-- In particular, a deleted closed segment contributes zero to every vertex
potential, as asserted in claim 54879. -/
theorem closed_segment_potential_sum_claim54879
    {α β : Type*} [AddCommGroup β] (f : α → β) (n : ℕ)
    (p : Fin (n + 1) → α) (hclosed : p 0 = p (Fin.last n)) :
    (∑ k : Fin n, (f (p k.castSucc) - f (p k.succ))) = 0 := by
  rw [potential_sum_telescope_claim54879, hclosed]
  exact sub_self _

end MathlibPlus.Combinatorics
