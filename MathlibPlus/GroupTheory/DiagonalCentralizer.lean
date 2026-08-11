import Mathlib

namespace MathlibPlus.GroupTheory

/--
Claim 37481.  The ambient group `W`, the embedded base group `G^p`, and the
coordinate-cycling top element `σ` are all explicit: `hconj` states that
conjugation by `σ` shifts the `Fin p` coordinates.  The conclusion is the
preimage in the base group of the actual centralizer of `{σ}`.
-/
theorem diagonalCentralizerOfCoordinateCycle
    {G W : Type*} [Group G] [Group W] {p : ℕ} [NeZero p]
    (ι : (Fin p → G) →* W) (σ : W)
    (hι : Function.Injective ι)
    (hconj : ∀ x : Fin p → G,
      σ * ι x * σ⁻¹ = ι (fun i => x (i + 1))) :
    {x : Fin p → G |
        ι x ∈ Subgroup.centralizer ({σ} : Set W)} =
      {x : Fin p → G | ∀ i j : Fin p, x i = x j} := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  ext x
  constructor
  · intro hx i j
    have hcomm : σ * ι x = ι x * σ := by
      exact (Subgroup.mem_centralizer_iff.mp hx) σ (by simp)
    have hfixed : (fun i : Fin (n + 1) => x (i + 1)) = x := by
      apply hι
      rw [← hconj x]
      calc
        σ * ι x * σ⁻¹ = (ι x * σ) * σ⁻¹ := by rw [hcomm]
        _ = ι x := by simp [mul_assoc]
    have hstep : ∀ k : Fin n, x k.castSucc = x k.succ := by
      intro k
      have hk := congrFun hfixed k.castSucc
      rw [show k.castSucc + 1 = k.succ by
        apply Fin.ext
        simp [Fin.add_def]] at hk
      exact hk.symm
    have hzero : ∀ k : Fin (n + 1), x k = x 0 := by
      intro k
      induction k using Fin.inductionOn with
      | zero => rfl
      | succ k ih =>
          exact (hstep k).symm.trans ih
    exact (hzero i).trans (hzero j).symm
  · intro hx
    have hfixed : (fun i : Fin (n + 1) => x (i + 1)) = x := by
      funext i
      exact hx _ _
    apply Subgroup.mem_centralizer_iff.mpr
    intro h hh
    simp only [Set.mem_singleton_iff] at hh
    subst h
    have hconj_eq : σ * ι x * σ⁻¹ = ι x := by
      rw [hconj]
      rw [hfixed]
    have hcomm : σ * ι x = ι x * σ := by
      calc
        σ * ι x = (σ * ι x * σ⁻¹) * σ := by simp [mul_assoc]
        _ = ι x * σ := by rw [hconj_eq]
    exact hcomm

end MathlibPlus.GroupTheory
