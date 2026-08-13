import MathlibPlus.Open.GroupTheory.OddCycleReflectionInterface
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace MathlibPlus.GroupTheory

/-- Odd transitive cycles with specified reversing involutions form a single
simultaneous conjugacy class. -/
theorem oddCycleReflectionInterface :
    MathlibPlus.Open.GroupTheory.oddCycleReflectionInterface := by
  intro p hpOdd c d ι κ hcTrans hdTrans hι2 hκ2 hιrev hκrev
  by_cases hp1 : p = 1
  · subst p
    have hc1 : c = 1 := Subsingleton.elim _ _
    have hd1 : d = 1 := Subsingleton.elim _ _
    have hι1 : ι = 1 := Subsingleton.elim _ _
    have hκ1 : κ = 1 := Subsingleton.elim _ _
    subst c
    subst d
    subst ι
    subst κ
    exact ⟨1, by simp⟩
  have hp2 : 2 ≤ p := by
    obtain ⟨q, hq⟩ := hpOdd
    omega
  have hp0 : 0 < p := by omega
  have hnotSubsingleton : ¬ Subsingleton (Fin p) := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_fin]
    omega
  have hcNoFix : ∀ x : Fin p, c x ≠ x := by
    intro x hcx
    apply hnotSubsingleton
    constructor
    intro y z
    obtain ⟨m, hm⟩ := hcTrans x y
    obtain ⟨n, hn⟩ := hcTrans x z
    calc
      y = (c ^ m) x := hm.symm
      _ = x := c.pow_apply_eq_self_of_apply_eq_self hcx m
      _ = (c ^ n) x := (c.pow_apply_eq_self_of_apply_eq_self hcx n).symm
      _ = z := hn
  have hdNoFix : ∀ x : Fin p, d x ≠ x := by
    intro x hdx
    apply hnotSubsingleton
    constructor
    intro y z
    obtain ⟨m, hm⟩ := hdTrans x y
    obtain ⟨n, hn⟩ := hdTrans x z
    calc
      y = (d ^ m) x := hm.symm
      _ = x := d.pow_apply_eq_self_of_apply_eq_self hdx m
      _ = (d ^ n) x := (d.pow_apply_eq_self_of_apply_eq_self hdx n).symm
      _ = z := hn
  let x0 : Fin p := ⟨0, hp0⟩
  have hcCycle : c.IsCycle := by
    refine ⟨x0, hcNoFix x0, ?_⟩
    intro y _hy
    obtain ⟨n, hn⟩ := hcTrans x0 y
    exact ⟨(n : ℤ), by simpa using hn⟩
  have hdCycle : d.IsCycle := by
    refine ⟨x0, hdNoFix x0, ?_⟩
    intro y _hy
    obtain ⟨n, hn⟩ := hdTrans x0 y
    exact ⟨(n : ℤ), by simpa using hn⟩
  have hcSupport : c.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => Equiv.Perm.mem_support.mpr (hcNoFix x)
  have hdSupport : d.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => Equiv.Perm.mem_support.mpr (hdNoFix x)
  obtain ⟨g, hgc⟩ := (_root_.isConj_iff).mp
    (hcCycle.isConj hdCycle (by rw [hcSupport, hdSupport]))
  have hnot2 : ¬ 2 ∣ Fintype.card (Fin p) := by
    rw [Fintype.card_fin]
    rintro ⟨q, hq⟩
    obtain ⟨r, hr⟩ := hpOdd
    omega
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (p := 2) (n := 1) hnot2 (by simpa [pow_two] using hι2)
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (p := 2) (n := 1) hnot2 (by simpa [pow_two] using hκ2)
  obtain ⟨m, hm⟩ := hdTrans (g a) b
  let h : Equiv.Perm (Fin p) := d ^ m * g
  have hha : h a = b := by
    simpa [h, Equiv.Perm.mul_apply] using hm
  have hhcd : h * c * h⁻¹ = d := by
    dsimp [h]
    calc
      (d ^ m * g) * c * (d ^ m * g)⁻¹ =
          d ^ m * (g * c * g⁻¹) * (d ^ m)⁻¹ := by group
      _ = d ^ m * d * (d ^ m)⁻¹ := by rw [hgc]
      _ = d := by group
  let σ : Equiv.Perm (Fin p) := h * ι * h⁻¹
  have hσfix : σ b = b := by
    rw [← hha]
    simp [σ, Equiv.Perm.mul_apply, ha]
  have hσ2 : σ * σ = 1 := by
    dsimp [σ]
    calc
      (h * ι * h⁻¹) * (h * ι * h⁻¹) = h * (ι * ι) * h⁻¹ := by group
      _ = 1 := by rw [hι2]; simp
  have hconjInv : h * c⁻¹ * h⁻¹ = d⁻¹ := by
    have hi := congrArg Inv.inv hhcd
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi
  have hσrev : σ * d * σ = d⁻¹ := by
    calc
      σ * d * σ = σ * (h * c * h⁻¹) * σ := by rw [hhcd]
      _ = h * (ι * c * ι) * h⁻¹ := by dsimp [σ]; group
      _ = h * c⁻¹ * h⁻¹ := by rw [hιrev]
      _ = d⁻¹ := hconjInv
  have hσd : σ * d = d⁻¹ * σ := by
    calc
      σ * d = σ * d * (σ * σ) := by rw [hσ2, mul_one]
      _ = (σ * d * σ) * σ := by group
      _ = d⁻¹ * σ := by rw [hσrev]
  have hκd : κ * d = d⁻¹ * κ := by
    calc
      κ * d = κ * d * (κ * κ) := by rw [hκ2, mul_one]
      _ = (κ * d * κ) * κ := by group
      _ = d⁻¹ * κ := by rw [hκrev]
  have hσpow : ∀ n : ℕ, σ * d ^ n = (d⁻¹) ^ n * σ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          σ * d ^ (n + 1) = (σ * d ^ n) * d := by rw [pow_succ]; group
          _ = ((d⁻¹) ^ n * σ) * d := by rw [ih]
          _ = (d⁻¹) ^ n * (σ * d) := by group
          _ = (d⁻¹) ^ n * (d⁻¹ * σ) := by rw [hσd]
          _ = (d⁻¹) ^ (n + 1) * σ := by rw [pow_succ]; group
  have hκpow : ∀ n : ℕ, κ * d ^ n = (d⁻¹) ^ n * κ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          κ * d ^ (n + 1) = (κ * d ^ n) * d := by rw [pow_succ]; group
          _ = ((d⁻¹) ^ n * κ) * d := by rw [ih]
          _ = (d⁻¹) ^ n * (κ * d) := by group
          _ = (d⁻¹) ^ n * (d⁻¹ * κ) := by rw [hκd]
          _ = (d⁻¹) ^ (n + 1) * κ := by rw [pow_succ]; group
  have hσapply (n : ℕ) (x : Fin p) :
      σ ((d ^ n) x) = ((d⁻¹) ^ n) (σ x) := by
    simpa only [Equiv.Perm.mul_apply] using congrArg (fun q : Equiv.Perm (Fin p) => q x) (hσpow n)
  have hκapply (n : ℕ) (x : Fin p) :
      κ ((d ^ n) x) = ((d⁻¹) ^ n) (κ x) := by
    simpa only [Equiv.Perm.mul_apply] using congrArg (fun q : Equiv.Perm (Fin p) => q x) (hκpow n)
  have hσκ : σ = κ := by
    apply Equiv.ext
    intro x
    obtain ⟨n, hn⟩ := hdTrans b x
    calc
      σ x = σ ((d ^ n) b) := by rw [hn]
      _ = ((d⁻¹) ^ n) (σ b) := hσapply n b
      _ = ((d⁻¹) ^ n) b := by rw [hσfix]
      _ = ((d⁻¹) ^ n) (κ b) := by rw [hb]
      _ = κ ((d ^ n) b) := (hκapply n b).symm
      _ = κ x := by rw [hn]
  refine ⟨h, hhcd, ?_⟩
  change σ = κ
  exact hσκ

end MathlibPlus.GroupTheory
