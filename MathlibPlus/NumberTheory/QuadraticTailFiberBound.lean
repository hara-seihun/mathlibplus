import Mathlib

namespace MathlibPlus.NumberTheory

/-- The quadratic congruence `u (u + 1) = b` has at most two residue
classes modulo a prime, and its representatives up to `X` satisfy the
coarse tail-fibre bound used in claim 35345. -/
theorem quadraticTailFiberBound_claim35345
    {p z X : ℕ} (hp : p.Prime) (_hzp : z < p) (b : ZMod p)
    (_hpX : p ≤ 2 * X + 1) :
    (Set.ncard {r : ZMod p | r * (r + 1) = b} ≤ 2) ∧
      (((Finset.range (X + 1)).filter
          (fun u : ℕ => (u : ZMod p) * ((u + 1 : ℕ) : ZMod p) = b)).card : ℝ)
        ≤ 2 * ((X + 1 : ℝ) / p) + 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hroot : Set.ncard {r : ZMod p | r * (r + 1) = b} ≤ 2 := by
    by_contra h
    have hgt : 2 < Set.ncard {r : ZMod p | r * (r + 1) = b} := Nat.lt_of_not_ge h
    obtain ⟨a, b', c, ha, hb, hc, hab, hac, hbc⟩ :=
      ((Set.two_lt_ncard_iff (s := {r : ZMod p | r * (r + 1) = b})).mp hgt)
    have habfac : (a - b') * (a + b' + 1) = 0 := by
      calc
        (a - b') * (a + b' + 1) = a * (a + 1) - b' * (b' + 1) := by ring
        _ = b - b := by rw [ha, hb]
        _ = 0 := sub_self b
    have hacfac : (a - c) * (a + c + 1) = 0 := by
      calc
        (a - c) * (a + c + 1) = a * (a + 1) - c * (c + 1) := by ring
        _ = b - b := by rw [ha, hc]
        _ = 0 := sub_self b
    have habsum : a + b' + 1 = 0 := by
      exact (mul_eq_zero.mp habfac).resolve_left (sub_ne_zero.mpr hab)
    have hacsum : a + c + 1 = 0 := by
      exact (mul_eq_zero.mp hacfac).resolve_left (sub_ne_zero.mpr hac)
    apply hbc
    have heq : a + b' + 1 = a + c + 1 := habsum.trans hacsum.symm
    have heq' := congrArg (fun t : ZMod p => t - (a + 1)) heq
    simpa [add_assoc, add_left_comm, add_comm] using heq'
  refine ⟨hroot, ?_⟩
  let R : Finset (ZMod p) := Finset.univ.filter (fun r => r * (r + 1) = b)
  have hRset : (Set.toFinite {r : ZMod p | r * (r + 1) = b}).toFinset = R := by
    ext r
    simp [R]
  have hRcard : R.card ≤ 2 := by
    have hcard : Set.ncard {r : ZMod p | r * (r + 1) = b} = R.card := by
      rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _), hRset]
    rw [← hcard]
    exact hroot
  let A : Finset ℕ := (Finset.range (X + 1)).filter
    (fun u : ℕ => (u : ZMod p) * ((u + 1 : ℕ) : ZMod p) = b)
  let f : ℕ → (ZMod p) × ℕ := fun u => ((u : ZMod p), u / p)
  have hf_maps : Set.MapsTo f A (R.product (Finset.range (X / p + 1))) := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have huX : u ≤ X := by
      have huLt : u < X + 1 := Finset.mem_range.mp hu'.1
      omega
    have huR : (u : ZMod p) ∈ R := by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [Nat.cast_add, Nat.cast_one] using hu'.2
    have huq : u / p < X / p + 1 := by
      exact Nat.lt_succ_of_le (Nat.div_le_div_right huX)
    exact Finset.mem_product.mpr ⟨huR, Finset.mem_range.mpr huq⟩
  have hf_inj : (A : Set ℕ).InjOn f := by
    intro u hu v hv huv
    have hres : (u : ZMod p) = (v : ZMod p) := congrArg Prod.fst huv
    have hmod : u % p = v % p :=
      (ZMod.natCast_eq_natCast_iff' u v p).mp hres
    have hdiv : u / p = v / p := congrArg Prod.snd huv
    calc
      u = u / p * p + u % p := (Nat.div_add_mod' u p).symm
      _ = v / p * p + v % p := by rw [hdiv, hmod]
      _ = v := Nat.div_add_mod' v p
  have hcard : A.card ≤ (R.product (Finset.range (X / p + 1))).card :=
    Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hnat : A.card ≤ 2 * (X / p + 1) := by
    calc
      A.card ≤ (R.product (Finset.range (X / p + 1))).card := hcard
      _ = R.card * (X / p + 1) := by simp
      _ ≤ 2 * (X / p + 1) := Nat.mul_le_mul_right _ hRcard
  have hreal : (A.card : ℝ) ≤ (2 * (X / p + 1) : ℕ) := by
    exact_mod_cast hnat
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdivreal : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / p := by
    simpa using (Nat.cast_div_le (α := ℝ) (m := X) (n := p))
  have hXdiv : (X : ℝ) / p ≤ (X + 1 : ℝ) / p := by
    apply div_le_div_of_nonneg_right
    · norm_num
    · exact hp0.le
  calc
    (((Finset.range (X + 1)).filter
        (fun u : ℕ => (u : ZMod p) * ((u + 1 : ℕ) : ZMod p) = b)).card : ℝ) =
        (A.card : ℝ) := by rfl
    _ ≤ (2 * (X / p + 1) : ℕ) := hreal
    _ = 2 * ((X / p : ℕ) : ℝ) + 2 := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    _ ≤ 2 * ((X + 1 : ℝ) / p) + 2 := by
      gcongr
      exact hdivreal.trans hXdiv

end MathlibPlus.NumberTheory
