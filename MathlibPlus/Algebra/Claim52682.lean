import Mathlib

open scoped Pointwise

namespace MathlibPlus.Algebra.Claim52682

/-- The componentwise linear shear in the separable two-line switch theorem.
The set-level formulation is the exact fibre-invariance core: each fibre is
translated by its relative-derivative span, and the shear carries the source
connection set to the target connection set. -/
theorem separableTwoLineSwitch_maps
    {A B : Type*}
    [AddCommGroup A] [Module (ZMod 3) A]
    [AddCommGroup B] [Module (ZMod 3) B]
    (p : A → ZMod 3) (q : B → ZMod 3)
    (hp0 : p 0 = 0) (hq0 : q 0 = 0)
    (hpOdd : ∀ a : A, p (-a) = -p a)
    (hqOdd : ∀ b : B, q (-b) = -q b)
    (S : (A × B) → Set (ZMod 3 × ZMod 3))
    (ellp : A →ₗ[ZMod 3] ZMod 3)
    (ellq : B →ₗ[ZMod 3] ZMod 3)
    (hellp : ∀ a : A,
      (∀ x : A, p (x + a) - p x - p a = 0) → ellp a = p a)
    (hellq : ∀ b : B,
      (∀ y : B, q (y + b) - q y - q b = 0) → ellq b = q b)
    (hS : ∀ u : A × B,
      S u + (↑(Submodule.span (ZMod 3) (Set.range (fun x : A × B =>
        (p (x.1 + u.1) - p x.1 - p u.1,
         q (x.2 + u.2) - q x.2 - q u.2))) : Set (ZMod 3 × ZMod 3))) = S u)
    (hSymm : ∀ u : A × B, S (-u) = -S u) :
    (fun z : (A × B) × (ZMod 3 × ZMod 3) =>
        (z.1, z.2 + (ellp z.1.1, ellq z.1.2))) ''
        {z | z.2 ∈ S z.1} =
      {z | ∃ s, s ∈ S z.1 ∧
        z.2 = s + (p z.1.1, q z.1.2)} := by
  classical
  let deriv : (A × B) → (A × B) → (ZMod 3 × ZMod 3) :=
    fun (u x : A × B) =>
    (p (x.1 + u.1) - p x.1 - p u.1,
     q (x.2 + u.2) - q x.2 - q u.2)
  let H : (A × B) → Submodule (ZMod 3) (ZMod 3 × ZMod 3) := fun u =>
    Submodule.span (ZMod 3) (Set.range (deriv u))
  have hspan (u : A × B) (x : A × B) : deriv u x ∈ H u := by
    exact Submodule.subset_span ⟨x, rfl⟩
  have haxis1_of_not (u : A × B)
      (ha : ¬ (∀ x : A, p (x + u.1) - p x - p u.1 = 0)) :
      (1, 0) ∈ H u := by
    obtain ⟨x, hx⟩ := Classical.not_forall.mp ha
    let d : ZMod 3 := p (x + u.1) - p x - p u.1
    have hd : d ≠ 0 := hx
    have hderiv : (d, 0) ∈ H u := by
      simpa [d, deriv, hp0, hq0] using hspan u (x, 0)
    have hscaled := (H u).smul_mem d⁻¹ hderiv
    simpa [smul_eq_mul, d, inv_mul_cancel₀ hd] using hscaled
  have haxis2_of_not (u : A × B)
      (hb : ¬ (∀ y : B, q (y + u.2) - q y - q u.2 = 0)) :
      (0, 1) ∈ H u := by
    obtain ⟨y, hy⟩ := Classical.not_forall.mp hb
    let d : ZMod 3 := q (y + u.2) - q y - q u.2
    have hd : d ≠ 0 := hy
    have hderiv : (0, d) ∈ H u := by
      simpa [d, deriv, hp0, hq0] using hspan u (0, y)
    have hscaled := (H u).smul_mem d⁻¹ hderiv
    simpa [smul_eq_mul, d, inv_mul_cancel₀ hd] using hscaled
  have hdef (u : A × B) :
      (ellp u.1, ellq u.2) - (p u.1, q u.2) ∈ H u := by
    have h1 : (ellp u.1 - p u.1, 0) ∈ H u := by
      by_cases ha : ∀ x : A, p (x + u.1) - p x - p u.1 = 0
      · have he := hellp u.1 ha
        have hz : ellp u.1 - p u.1 = 0 := sub_eq_zero.mpr he
        rw [hz]
        exact (H u).zero_mem
      · have haxis := haxis1_of_not u ha
        simpa [smul_eq_mul] using (H u).smul_mem (ellp u.1 - p u.1) haxis
    have h2 : (0, ellq u.2 - q u.2) ∈ H u := by
      by_cases hb : ∀ y : B, q (y + u.2) - q y - q u.2 = 0
      · have he := hellq u.2 hb
        have hz : ellq u.2 - q u.2 = 0 := sub_eq_zero.mpr he
        rw [hz]
        exact (H u).zero_mem
      · have haxis := haxis2_of_not u hb
        simpa [smul_eq_mul] using (H u).smul_mem (ellq u.2 - q u.2) haxis
    have hadd := (H u).add_mem h1 h2
    simpa [Prod.sub_def] using hadd
  have hmem (u : A × B) {s : ZMod 3 × ZMod 3}
      (hs : s ∈ S u) {h : ZMod 3 × ZMod 3} (hh : h ∈ H u) :
      s + h ∈ S u := by
    have hu : S u + (H u : Set (ZMod 3 × ZMod 3)) = S u := by
      simpa [H, deriv] using hS u
    rw [← hu]
    exact Set.mem_add.mpr ⟨s, hs, h, hh, rfl⟩
  have hdef' (u : A × B) :
      (p u.1, q u.2) - (ellp u.1, ellq u.2) ∈ H u := by
    have hn := (H u).neg_mem (hdef u)
    convert hn using 1 <;> abel
  apply Set.ext
  intro z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y.2 ∈ S y.1 at hy
    change ∃ s, s ∈ S y.1 ∧
      y.2 + (ellp y.1.1, ellq y.1.2) =
        s + (p y.1.1, q y.1.2)
    let h := (ellp y.1.1, ellq y.1.2) - (p y.1.1, q y.1.2)
    refine ⟨y.2 + h, hmem y.1 hy (by simpa [h] using hdef y.1), ?_⟩
    apply Prod.ext
    · dsimp [h]
      abel
    · dsimp [h]
      abel
  · intro hz
    change ∃ s, s ∈ S z.1 ∧ z.2 = s + (p z.1.1, q z.1.2) at hz
    rcases hz with ⟨s, hs, hz⟩
    let h := (p z.1.1, q z.1.2) - (ellp z.1.1, ellq z.1.2)
    refine ⟨(z.1, z.2 - (ellp z.1.1, ellq z.1.2)), ?_, ?_⟩
    · change z.2 - (ellp z.1.1, ellq z.1.2) ∈ S z.1
      rw [hz]
      have hm := hmem z.1 hs (by simpa [h] using hdef' z.1)
      convert hm using 1
      apply Prod.ext
      · dsimp [h]
        abel
      · dsimp [h]
        abel
    · apply Prod.ext
      · rfl
      · simp

end MathlibPlus.Algebra.Claim52682
