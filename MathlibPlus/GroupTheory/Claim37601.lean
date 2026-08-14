import Mathlib

namespace MathlibPlus.GroupTheory

/-- The averaging proof of the vanishing of first cohomology when the group
cardinality acts bijectively on the finite additive module. -/
theorem oneCocycle_isCoboundary_claim37601
    {Q M : Type*} [Group Q] [Fintype Q] [AddCommGroup M]
    [Fintype M] [DistribMulAction Q M]
    (hcard : Function.Bijective (fun x : M => Fintype.card Q • x))
    (f : Q → M)
    (hf : ∀ g h : Q, f (g * h) = f g + g • f h) :
    ∃ m : M, ∀ g : Q, f g = m - g • m := by
  classical
  let s : M := ∑ h : Q, f h
  obtain ⟨m, hm⟩ := hcard.2 s
  refine ⟨m, ?_⟩
  intro g
  apply hcard.1
  have hsum :
      (Fintype.card Q) • f g + g • s = s := by
    calc
      (Fintype.card Q) • f g + g • s =
          ∑ h : Q, (f g + g • f h) := by
            simp [s, Finset.sum_add_distrib, Finset.smul_sum]
      _ = ∑ h : Q, f (g * h) := by
            apply Finset.sum_congr rfl
            intro h _
            exact (hf g h).symm
      _ = s := by
            simpa [s] using
              (Fintype.sum_equiv (Equiv.mulLeft g)
                (fun h : Q => f (g * h)) f (fun _ => rfl))
  calc
    (Fintype.card Q) • f g = s - g • s := by
      calc
        (Fintype.card Q) • f g =
            ((Fintype.card Q) • f g + g • s) - g • s := by abel
        _ = s - g • s := by rw [hsum]
    _ = (Fintype.card Q) • (m - g • m) := by
      rw [← hm]
      have hcomm : ∀ n : ℕ, g • (n • m) = n • (g • m) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [succ_nsmul, smul_add, ih, succ_nsmul]
      rw [hcomm]
      simp [smul_sub]

end MathlibPlus.GroupTheory
